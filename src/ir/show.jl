# Structured IR pretty printing.

function Base.show(io::IO, ::MIME"text/plain", sci::StructuredIRCode)
    println(io, "StructuredIRCode(")

    # Show debug info only when line_map is populated (empty!(sci.line_map) strips it).
    lineinfo = isempty(sci.line_map) ? nothing : LineInfoTracker(sci)
    base_p = IRPrinter(io, sci.max_ssa_idx; lineinfo)
    # The entry block uses a "│ " prefix (2 chars, not 4).
    p = child_printer(base_p, sci.entry, "│ ")

    # is_closing_self=true makes the last item replace │ with └── rather than
    # appending └── after │.
    print_block_body(p, sci.entry; is_closing_self=true)

    print(io, ")")
end

# string() uses the same detailed format, as CodeInfo does.
function Base.show(io::IO, sci::StructuredIRCode)
    show(io, MIME"text/plain"(), sci)
end

mutable struct LineInfoTracker
    sci::StructuredIRCode
    last_loc::SourceLocation      # last printed location, to suppress duplicates
end

LineInfoTracker(sci::StructuredIRCode) =
    LineInfoTracker(sci, SourceLocation(nothing, Symbol(""), Int32(0)))

"""
    IRPrinter

Context for printing structured IR with indentation and value formatting,
following Julia's IRCode style with box-drawing characters.
"""
mutable struct IRPrinter
    io::IO
    indent::Int
    line_prefix::String    # prefix for continuation lines (│, spaces)
    max_idx_width::Int     # width of "%N = " for alignment
    color::Bool
    lineinfo::Union{Nothing, LineInfoTracker}
end

function IRPrinter(io::IO, max_ssa_idx::Int; lineinfo=nothing)
    # Width of "%N = " for the widest index: % + digits + space + = + space.
    max_idx_width = ndigits(max_ssa_idx) + 4
    color = get(io, :color, false)::Bool
    IRPrinter(io, 0, "", max_idx_width, color, lineinfo)
end

function indent(p::IRPrinter, n::Int=1)
    new_prefix = p.line_prefix * "  "  # 2 spaces per indent level
    return IRPrinter(p.io, p.indent + n, new_prefix, p.max_idx_width, p.color, p.lineinfo)
end

# Child printer for a nested Block. SSA indices are global, so max_idx_width carries over.
function child_printer(p::IRPrinter, nested_block::Block, cont_prefix::String)
    IRPrinter(p.io, p.indent + 1, p.line_prefix * cont_prefix, p.max_idx_width, p.color, p.lineinfo)
end

# Emit a "@ file:line within `method`" annotation when the location changed.
function emit_lineinfo!(p::IRPrinter, ssa_idx::Int)
    li = p.lineinfo
    li === nothing && return
    locs = source_location(li.sci, ssa_idx)
    isempty(locs) && return
    loc = last(locs)  # innermost frame
    loc == li.last_loc && return
    li.last_loc = loc
    print_indent(p)
    m = loc.method
    m isa MethodInstance && (m = m.def)
    m isa Method && (m = m.name)
    name = m isa Symbol ? string(m) : ""
    print_colored(p, "@ $(loc.file):$(loc.line)", :yellow)
    !isempty(name) && print_colored(p, " within `$name`", :yellow)
    println(p.io)
end

# Print a region header: "├ label:", or "└ label:" for the last/empty region.
function print_region_header(p::IRPrinter, label::String, args::Vector{BlockArgument}; is_last::Bool=false)
    print_indent(p)
    print_colored(p, is_last ? "└" : "├", :light_black)
    print(p.io, " ", label)
    if !isempty(args)
        print(p.io, "(")
        for (i, arg) in enumerate(args)
            i > 1 && print(p.io, ", ")
            print(p.io, "%arg", arg.id)
            print_colored(p, string("::", format_type(arg.type)), :cyan)
        end
        print(p.io, ")")
    end
    println(p.io, ":")
end

function print_indent(p::IRPrinter)
    # Color the line prefix (box-drawing characters from parent blocks).
    print_colored(p, p.line_prefix, :light_black)
end

function print_colored(p::IRPrinter, s, color::Symbol)
    if p.color
        printstyled(p.io, s; color=color)
    else
        print(p.io, s)
    end
end

# Print an IR value (no special coloring, like Julia's code_typed).
function print_value(p::IRPrinter, v::SSAValue)
    print(p.io, "%", v.id)
end

function print_value(p::IRPrinter, v::BlockArgument)
    print(p.io, "%arg", v.id)
end

function print_value(p::IRPrinter, v::Argument)
    # IRCode has no slot names, so print arguments as _N.
    print(p.io, "_", v.n)
end

function print_value(p::IRPrinter, v::SlotNumber)
    print(p.io, "slot#", v.id)
end

function print_value(p::IRPrinter, v::Undef)
    print(p.io, "undef")
end

function print_value(p::IRPrinter, v::QuoteNode)
    print(p.io, repr(v.value))
end

function print_value(p::IRPrinter, v::GlobalRef)
    print(p.io, v.mod, ".", v.name)
end

function print_value(p::IRPrinter, v)
    print(p.io, repr(v))
end

# Format a type for printing (compact form).
function format_type(t)
    if t isa Core.Const
        string("Const(", repr(t.val), ")")
    else
        string(t)
    end
end

function is_intrinsic_call(func)
    if func isa GlobalRef
        try
            f = getfield(func.mod, func.name)
            return f isa Core.IntrinsicFunction
        catch
            return false
        end
    end
    return false
end

# Print an expression (RHS of a statement).
function print_expr(p::IRPrinter, expr::Expr)
    if expr.head == :call
        func = expr.args[1]
        args = expr.args[2:end]
        if is_intrinsic_call(func)
            print_colored(p, "intrinsic ", :light_black)
        end
        print_value(p, func)
        print(p.io, "(")
        for (i, a) in enumerate(args)
            i > 1 && print(p.io, ", ")
            print_value(p, a)
        end
        print(p.io, ")")
    elseif expr.head == :invoke
        mi = expr.args[1]
        func = expr.args[2]
        args = expr.args[3:end]
        print_colored(p, "invoke ", :light_black)
        if mi isa Core.MethodInstance
            print(p.io, mi.def.name)
            # Argument types from the MethodInstance signature.
            sig = mi.specTypes isa DataType ? mi.specTypes.parameters : ()
            print(p.io, "(")
            for (i, a) in enumerate(args)
                i > 1 && print(p.io, ", ")
                print_value(p, a)
                # sig position 1 is the function type, so argument i is at sig[i+1].
                if i + 1 <= length(sig)
                    print_colored(p, string("::", sig[i + 1]), :cyan)
                end
            end
            print(p.io, ")")
        else
            print_value(p, func)
            print(p.io, "(")
            for (i, a) in enumerate(args)
                i > 1 && print(p.io, ", ")
                print_value(p, a)
            end
            print(p.io, ")")
        end
    elseif expr.head == :new
        print(p.io, "new ", expr.args[1], "(")
        for (i, a) in enumerate(expr.args[2:end])
            i > 1 && print(p.io, ", ")
            print_value(p, a)
        end
        print(p.io, ")")
    elseif expr.head == :foreigncall
        print(p.io, "foreigncall ", repr(expr.args[1]))
    elseif expr.head == :boundscheck
        print(p.io, "boundscheck")
    else
        print(p.io, expr.head, " ")
        for (i, a) in enumerate(expr.args)
            i > 1 && print(p.io, ", ")
            print_value(p, a)
        end
    end
end

function print_expr(p::IRPrinter, v)
    print_value(p, v)
end

# Print initial values (carries) with their types.
function print_init_values(p::IRPrinter, carry_args::Vector{BlockArgument}, init_values::Vector{IRValue})
    if isempty(carry_args)
        return
    end
    print(p.io, " init(")
    for (i, (arg, init)) in enumerate(zip(carry_args, init_values))
        i > 1 && print(p.io, ", ")
        # Same %arg naming as print_value(BlockArgument).
        print(p.io, "%arg", arg.id, " = ")
        print_value(p, init)
        print_colored(p, string("::", format_type(arg.type)), :cyan)
    end
    print(p.io, ")")
end

function print_loop_args(p::IRPrinter, block_args::Vector{BlockArgument}, init_values::Vector{IRValue})
    print_init_values(p, block_args, init_values)
end

# Print a terminator. When is_last_in_block is true, replace the trailing │
# with └ to close the block.
function print_terminator(p::IRPrinter, term::ReturnNode; is_last_in_block::Bool=false)
    if is_last_in_block && endswith(p.line_prefix, "│   ")
        closing_prefix = chop(p.line_prefix; tail=4)
        print_colored(p, closing_prefix, :light_black)
        print_colored(p, "└   ", :light_black)
    else
        print_indent(p)
    end
    print(p.io, "return")
    if isdefined(term, :val)
        print(p.io, " ")
        print_value(p, term.val)
    end
    println(p.io)
end

function print_terminator(p::IRPrinter, term::Union{YieldOp,ContinueOp,BreakOp,ConditionOp}; is_last_in_block::Bool=false)
    if is_last_in_block && endswith(p.line_prefix, "│   ")
        closing_prefix = chop(p.line_prefix; tail=4)
        print_colored(p, closing_prefix, :light_black)
        print_colored(p, "└   ", :light_black)
    else
        print_indent(p)
    end
    print_terminator_content(p, term)
    println(p.io)
end

function print_terminator(p::IRPrinter, ::Nothing; is_last_in_block::Bool=false)
    # No terminator.
end

# Print a terminator that closes the block itself: replace the trailing │ with └.
function print_terminator_closing_self(p::IRPrinter, term)
    # Replace a trailing "│ " or "│   " in the prefix with "└ ".
    if endswith(p.line_prefix, "│   ")
        closing_prefix = chop(p.line_prefix; tail=4)
        print_colored(p, closing_prefix, :light_black)
        print_colored(p, "└ ", :light_black)
    elseif endswith(p.line_prefix, "│ ")
        closing_prefix = chop(p.line_prefix; tail=2)
        print_colored(p, closing_prefix, :light_black)
        print_colored(p, "└ ", :light_black)
    else
        print_indent(p)
    end
    print_terminator_content(p, term)
    println(p.io)
end

# Print an expression with its type annotation (no box-drawing, just indent).
function print_expr_with_type(p::IRPrinter, idx::Int, expr, typ)
    print_indent(p)

    # The "%N = " assignment, padded to align the widest index. -4 covers "% = ".
    idx_s = string(idx)
    pad = " "^(p.max_idx_width - length(idx_s) - 4)
    print(p.io, "%", idx_s, pad, " = ")
    print_expr(p, expr)

    print_colored(p, string("::", format_type(typ)), :cyan)
    println(p.io)
end

# Print a Block's contents.
# is_last_in_parent: the terminator closes with └── (added after the prefix).
# is_closing_self: the last item replaces the trailing │ with └── (for the entry block).
function print_block_body(p::IRPrinter, block::Block; is_last_in_parent::Bool=false, is_closing_self::Bool=false)
    items = []
    for (idx, entry) in block.body
        if entry.stmt isa ControlFlowOp
            push!(items, (:nested, idx, entry.stmt, entry.type))
        else
            push!(items, (:expr, idx, entry.stmt, entry.type))
        end
    end
    if block.terminator !== nothing
        push!(items, (:term, block.terminator))
    end

    for (i, item) in enumerate(items)
        is_last = (i == length(items))
        if item[1] == :expr
            emit_lineinfo!(p, item[2])
            print_expr_with_type(p, item[2], item[3], item[4])
        elseif item[1] == :nested
            emit_lineinfo!(p, item[2])
            # Control flow ops handle their own box-drawing.
            print_control_flow(p, item[3], item[2], item[4]; is_last=is_last && is_last_in_parent)
        else  # :term
            if is_last && is_closing_self
                print_terminator_closing_self(p, item[2])
            else
                # The terminator gets └── only as the last item while closing the parent.
                print_terminator(p, item[2]; is_last_in_block=is_last && is_last_in_parent)
            end
        end
    end
end

# Print just the terminator content (keyword + values), no prefix or newline.
function print_terminator_content(p::IRPrinter, term::YieldOp)
    print_colored(p, "yield", :yellow)
    print_terminator_values(p, term.values)
end
function print_terminator_content(p::IRPrinter, term::ContinueOp)
    print_colored(p, "continue", :yellow)
    print_terminator_values(p, term.values)
end
function print_terminator_content(p::IRPrinter, term::BreakOp)
    print_colored(p, "break", :yellow)
    print_terminator_values(p, term.values)
end
function print_terminator_content(p::IRPrinter, term::ConditionOp)
    print_colored(p, "condition", :yellow)
    print(p.io, "(")
    print_value(p, term.condition)
    print(p.io, ")")
    print_terminator_values(p, term.args)
end
function print_terminator_content(p::IRPrinter, term::ReturnNode)
    print(p.io, "return")
    if isdefined(term, :val)
        print(p.io, " ")
        print_value(p, term.val)
    end
end

function print_terminator_values(p::IRPrinter, values)
    if !isempty(values)
        print(p.io, " ")
        for (i, v) in enumerate(values)
            i > 1 && print(p.io, ", ")
            print_value(p, v)
        end
    end
end

# Print a ControlFlowOp, dispatching on the concrete op type.
print_control_flow(p::IRPrinter, op::IfOp, pos::Int, @nospecialize(result_type); is_last::Bool=false) = print_if_op_final(p, op, pos, result_type; is_last)
print_control_flow(p::IRPrinter, op::ForOp, pos::Int, @nospecialize(result_type); is_last::Bool=false) = print_for_op_final(p, op, pos, result_type; is_last)
print_control_flow(p::IRPrinter, op::WhileOp, pos::Int, @nospecialize(result_type); is_last::Bool=false) = print_while_op_final(p, op, pos, result_type; is_last)
print_control_flow(p::IRPrinter, op::LoopOp, pos::Int, @nospecialize(result_type); is_last::Bool=false) = print_loop_op_final(p, op, pos, result_type; is_last)

function print_if_op_final(p::IRPrinter, op::IfOp, pos::Int, @nospecialize(result_type); is_last::Bool=false)
    # The if header (no box-drawing prefix for the op itself).
    print_indent(p)
    idx_s = string(pos)
    pad = " "^(p.max_idx_width - length(idx_s) - 4)
    print(p.io, "%", idx_s, pad, " = if ")
    print_value(p, op.condition)

    if result_type !== nothing
        print_colored(p, " -> ", :light_black)
        print_colored(p, string(result_type), :cyan)
    end

    println(p.io)

    else_is_empty = isempty(op.else_region.body) && op.else_region.terminator === nothing

    # "then:" region header at the same level as the if, then its body one level in.
    # When else is empty, then's last item closes the if with └──.
    print_region_header(p, "then", op.then_region.args; is_last=false)
    then_body_p = child_printer(p, op.then_region, "│   ")
    print_block_body(then_body_p, op.then_region; is_last_in_parent=else_is_empty)

    if else_is_empty
        # Empty else: a lone "└ else:" closes the if.
        print_region_header(p, "else", op.else_region.args; is_last=true)
    else
        print_region_header(p, "else", op.else_region.args; is_last=false)
        else_body_p = child_printer(p, op.else_region, "│   ")
        print_block_body(else_body_p, op.else_region; is_last_in_parent=true)
    end
end

function print_for_op_final(p::IRPrinter, op::ForOp, pos::Int, @nospecialize(result_type); is_last::Bool=false)
    cont_prefix = is_last ? "    " : "│   "

    # The for header (no box-drawing prefix).
    print_indent(p)
    idx_s = string(pos)
    pad = " "^(p.max_idx_width - length(idx_s) - 4)
    print(p.io, "%", idx_s, pad, " = ")
    print_colored(p, "for", :yellow)
    print(p.io, " %arg", op.iv_arg.id, " = ")
    print_value(p, op.lower)
    print(p.io, ":")
    print_value(p, op.step)
    print(p.io, ":")
    print_value(p, op.upper)

    if !isempty(op.body.args)
        print_loop_args(p, op.body.args, op.init_values)
    end

    if result_type !== nothing
        print_colored(p, " -> ", :light_black)
        print_colored(p, string(result_type), :cyan)
    end

    println(p.io)

    # The body's continue terminator closes the for block with └──.
    body_p = child_printer(p, op.body, cont_prefix)
    print_block_body(body_p, op.body; is_last_in_parent=true)
end

function print_loop_op_final(p::IRPrinter, op::LoopOp, pos::Int, @nospecialize(result_type); is_last::Bool=false)
    cont_prefix = is_last ? "    " : "│   "

    # The loop header (no box-drawing prefix).
    print_indent(p)
    idx_s = string(pos)
    pad = " "^(p.max_idx_width - length(idx_s) - 4)
    print(p.io, "%", idx_s, pad, " = ")
    print_colored(p, "loop", :yellow)
    print_loop_args(p, op.body.args, op.init_values)
    if result_type !== nothing
        print_colored(p, " -> ", :light_black)
        print_colored(p, string(result_type), :cyan)
    end
    println(p.io)

    # The body's terminator closes the loop block with └──.
    body_p = child_printer(p, op.body, cont_prefix)
    print_block_body(body_p, op.body; is_last_in_parent=true)
end

function print_while_op_final(p::IRPrinter, op::WhileOp, pos::Int, @nospecialize(result_type); is_last::Bool=false)
    # The while header (no box-drawing prefix).
    print_indent(p)
    idx_s = string(pos)
    pad = " "^(p.max_idx_width - length(idx_s) - 4)
    print(p.io, "%", idx_s, pad, " = ")
    print_colored(p, "while", :yellow)
    print_loop_args(p, op.before.args, op.init_values)
    if result_type !== nothing
        print_colored(p, " -> ", :light_black)
        print_colored(p, string(result_type), :cyan)
    end
    println(p.io)

    do_is_empty = isempty(op.after.body) && op.after.terminator === nothing

    # "before" region header at the same level as the while, then its body one level in.
    # When the do region is empty, before's last item closes the while with └──.
    print_region_header(p, "before", op.before.args; is_last=false)
    before_body_p = child_printer(p, op.before, "│   ")
    print_block_body(before_body_p, op.before; is_last_in_parent=do_is_empty)

    # "do" region header: └ when empty (nothing follows), ├ when it has content.
    print_region_header(p, "do", op.after.args; is_last=do_is_empty)
    if !do_is_empty
        after_body_p = child_printer(p, op.after, "│   ")
        print_block_body(after_body_p, op.after; is_last_in_parent=true)
    end
end
