// Author: Ivan Kazmenko (gassa@mail.ru)
module runner;
import std.algorithm;
import std.conv;
import std.exception;
import std.range;
import std.stdio;
import std.string;
import language;
import parser;

import core.atomic : atomicLoad, atomicStore;
import core.sync.mutex : Mutex;
import core.sync.condition : Condition;
import core.thread : ThreadGroup;
import std.container.array : Array;
import std.container.binaryheap : BinaryHeap;

struct Msg
{
    ulong microtick; // priority key
    uint  seq;       // tie-break inside same microtick (preserve send(v1,v2,...) order)
    long  value;
}

alias MsgHeap = BinaryHeap!(
    Array!Msg,
    "a.microtick > b.microtick || (a.microtick == b.microtick && a.seq > b.seq)"
); // this comparator makes it a min-heap by microtick (see BinaryHeap docs) :contentReference[oaicite:2]{index=2}

final class Mailbox
{
private:
    Mutex mtx;
    Condition cv;
    MsgHeap heap;
    uint seqCounter;

public:
    this()
    {
        mtx = new Mutex;
        cv  = new Condition(mtx);
        heap = MsgHeap(Array!Msg.init);
        seqCounter = 0;
    }

    void push(ulong microtick, long value)
    {
        synchronized (mtx)
        {
            heap.insert(Msg(microtick, seqCounter, value));
            seqCounter += 1;
            cv.notify();
        }
    }

    // Wait until non-empty and return the *current* smallest microtick without popping
    ulong waitFrontMicrotick()
    {
        synchronized (mtx)
        {
            while (heap.empty)
            {
                cv.wait();
            }
            return heap.front.microtick;
        }
    }

    Msg popFront()
    {
        synchronized (mtx)
        {
            // caller guarantees non-empty
            auto msg = heap.front;
            heap.removeFront();
            return msg;
        }
    }

	void notifyAll()
	{
		synchronized (mtx)
		{
			cv.notifyAll();
		}
	}
}

class Runner
{
	struct Var
	{
		long value;
		bool isConst;

		this (long value_, bool isConst_ = false)
		{
			value = value_;
			isConst = isConst_;
		}

		@disable this (this);
	}

	struct Array
	{
		long [] contents;
		bool isConst;

		this (long [] contents_, bool isConst_ = false)
		{
			contents = contents_;
			isConst = isConst_;
		}

		@disable this (this);
	}

	struct Context
	{
		Statement parent;
		int pos;
		Statement [] block;
		Var [string] vars;
		Array [string] arrays;
	}

	RunnerControl control;
	int id;

	Context [] state;
	int delay;
	ulong microtick;

	this (Args...) (RunnerControl control_, int id_,
	    FunctionBlock p, Args args)
	{
		control = control_;
		id = id_;

		state = [Context (p, -1)];
		delay = 0;
		microtick = cast(ulong)id;
		int argNum = 0;

		if (p.parameterList.length >= 1)
		{
			state.back.vars[p.parameterList[argNum]] = Var(cast(long)id, true);
			argNum += 1;
		}
		if (p.parameterList.length >= 2)
		{
			state.back.vars[p.parameterList[argNum]] = Var(cast(long)control.num, true);
			argNum += 1;
		}

		static foreach (cur; args)
		{
			if (argNum >= p.parameterList.length)
			{
				throw new Exception("too many parameters");
			}

			static if (is (typeof(cur) : long))
			{
				state.back.vars[p.parameterList[argNum]] = Var(cur, true);
			}
			else static if (is (typeof(cur) : long[]))
			{
				state.back.arrays[p.parameterList[argNum]] = Array(cur, true);
			}
			else
			{
				static assert(false);
			}

			argNum += 1;
		}

		if (argNum < p.parameterList.length)
		{
			throw new Exception("not enough parameters");
		}
	}

	long * varAddress (string name, bool canCreate = false)
	{
		foreach_reverse (ref cur; state)
		{
			if (name in cur.vars)
			{
				if (cur.vars[name].isConst)
				{
					throw new Exception ("variable " ~ name ~
					    " is constant");
				}
				return &(cur.vars[name].value);
			}
		}
		if (!canCreate)
		{
			throw new Exception ("no such variable: " ~ name);
		}
		state.back.vars[name] = Var (0);
		return &(state.back.vars[name].value);
	}

	long * arrayAddress (string name, long index)
	{
		foreach_reverse (ref cur; state)
		{
			if (name in cur.arrays)
			{
				if (cur.arrays[name].isConst)
				{
					throw new Exception ("array " ~ name ~
					    " is constant");
				}
				if (index < 0 ||
				    cur.arrays[name].contents.length <= index)
				{
					throw new Exception ("array " ~ name ~
					    ": no index " ~ index.text);
				}
				return &(cur.arrays[name]
				    .contents[index.to !(size_t)]);
			}
		}
		throw new Exception ("no such array: " ~ name);
	}

	long varValue (string name)
	{
		foreach_reverse (ref cur; state)
		{
			if (name in cur.vars)
			{
				return cur.vars[name].value;
			}
		}
		throw new Exception ("no such variable: " ~ name);
	}

	long arrayValue (string name, long index)
	{
		foreach_reverse (ref cur; state)
		{
			if (name in cur.arrays)
			{
				if (index < 0 ||
				    cur.arrays[name].contents.length <= index)
				{
					throw new Exception ("array " ~ name ~
					    ": no index " ~ index.text);
				}
				return cur.arrays[name]
				    .contents[index.to !(size_t)];
			}
		}
		throw new Exception ("no such array: " ~ name);
	}

	long evalCall (CallExpression call)
	{
		auto values = call.argumentList
		    .map !(e => evalExpression (e)).array;

		if (call.name == "send")
		{
			if (values.length < 1)
				throw new Exception("send: no first argument");

			if (values[0] < 0 || control.num <= values[0])
				throw new Exception("send: first argument " ~ values[0].text ~
					" not in [0.." ~ control.num.text ~ ")");

			auto toId = values[0].to!(size_t);

			foreach (value; values[1..$])
			{
				control.queues[id][toId].push(microtick, value);
			}
			return 0;
		}

		if (call.name == "receive")
		{
			throw new Exception ("can only assign with receive");
		}

		if (call.name == "array")
		{
			throw new Exception ("can only assign with array");
		}

		if (call.name == "print")
		{
			synchronized (control.printMtx)
			{
				writefln !("%(%s %)") (values);
				stdout.flush();
			}
			return 0;
		}

		throw new Exception ("call of non-existing function: " ~
		    call.name);
	}

	long evalExpression (Expression e)
	{
		auto cur0 = cast (BinaryOpExpression) (e);
		if (cur0 !is null) with (cur0)
		{
			auto leftValue = evalExpression (left);
			auto rightValue = evalExpression (right);
			final switch (type)
			{
			case Type.add:          return leftValue + rightValue;
			case Type.subtract:     return leftValue - rightValue;
			case Type.multiply:     return leftValue * rightValue;
			case Type.divide:       return leftValue / rightValue;
			case Type.modulo:       return leftValue % rightValue;
			case Type.xor:          return leftValue ^ rightValue;
			case Type.and:          return leftValue & rightValue;
			case Type.or:           return leftValue | rightValue;
			case Type.greater:      return leftValue > rightValue;
			case Type.greaterEqual: return leftValue >= rightValue;
			case Type.less:         return leftValue < rightValue;
			case Type.lessEqual:    return leftValue <= rightValue;
			case Type.equal:        return leftValue == rightValue;
			case Type.notEqual:     return leftValue != rightValue;
			case Type.sar:          return leftValue >> rightValue;
			case Type.shr:          return (cast (ulong)
			    (leftValue)) >> rightValue;
			case Type.shl:          return leftValue << rightValue;
			}
		}

		auto cur1 = cast (UnaryOpExpression) (e);
		if (cur1 !is null) with (cur1)
		{
			auto value = evalExpression (expr);
			final switch (type)
			{
			case Type.plus:       return +value;
			case Type.minus:      return -value;
			case Type.not:        return !value;
			case Type.complement: return ~value;
			}
		}

		auto cur2 = cast (VarExpression) (e);
		if (cur2 !is null) with (cur2)
		{
			if (index is null)
			{
				return varValue (name);
			}
			else
			{
				auto indexValue = evalExpression (index);
				return arrayValue (name, indexValue);
			}
		}

		auto cur3 = cast (ConstExpression) (e);
		if (cur3 !is null) with (cur3)
		{
			return value;
		}

		auto cur4 = cast (CallExpression) (e);
		if (cur4 !is null) with (cur4)
		{
			return evalCall (cur4);
		}

		assert (false);
	}

	long * getAddr (VarExpression dest, bool canCreate)
	{
		long * res;
		if (dest.index is null)
		{
			res = varAddress (dest.name, canCreate);
		}
		else
		{
			auto indexValue = evalExpression (dest.index);
			res = arrayAddress (dest.name, indexValue);
		}
		return res;
	}

	void doAssign (AssignStatement cur, long * addr, long value)
	{
		with (cur) final switch (type)
		{
		case Type.assign:         *(addr) = value; break;
		case Type.assignAdd:      *(addr) += value; break;
		case Type.assignSubtract: *(addr) -= value; break;
		case Type.assignMultiply: *(addr) *= value; break;
		case Type.assignDivide:   *(addr) /= value; break;
		case Type.assignModulo:   *(addr) %= value; break;
		case Type.assignXor:      *(addr) ^= value; break;
		case Type.assignAnd:      *(addr) &= value; break;
		case Type.assignOr:       *(addr) |= value; break;
		case Type.assignSar:      *(addr) >>= value; break;
		case Type.assignShr:      *(cast (ulong *) (addr)) >>= value;
		    break;
		case Type.assignShl:      *(addr) <<= value; break;
		}
	}

void runStatementReceive (AssignStatement cur, CallExpression call)
{
    auto values = call.argumentList.map!(e => evalExpression(e)).array;

    if (values.length < 1)
        throw new Exception("receive: no first argument");
    if (values[0] < 0 || control.num <= values[0])
        throw new Exception("receive: first argument " ~ values[0].text ~
            " not in [0.." ~ control.num.text ~ ")");
    if (values.length > 1)
        throw new Exception("receive: more than one argument");

    auto otherId = values[0].to!(size_t);

    // ---- Phase A: wait until safe ----
    bool isSafe ()
    {
        foreach (j; 0 .. control.num)
        {
            if (j == id) continue;
            auto t = atomicLoad(control.nextMicrotick[j]);
            if (t <= microtick) return false;
        }
        return true;
    };

    synchronized (control.progressMtx)
    {
        while (!control.hasError && !isSafe())
        {
            control.progressCv.wait();
        }
        if (control.hasError)
            throw new Exception(control.errorMsg);
    }

    // ---- Phase B: wait for data (priority by microtick) ----
    // Wait mailbox to become non-empty and look at smallest timestamp
    auto frontTick = control.queues[otherId][id].waitFrontMicrotick();

    // If message is from the future relative to our microtick,
    // jump forward to first microtick strictly greater than frontTick.
    if (frontTick >= microtick)
    {
        while (microtick <= frontTick)
            microtick += cast(ulong)control.num;

        atomicStore(control.nextMicrotick[id], microtick);

        synchronized (control.progressMtx)
        {
            control.progressCv.notifyAll();
        }

        // After time jump, we must re-check safety (Phase A) again
        synchronized (control.progressMtx)
        {
            while (!control.hasError && !isSafe())
            {
                control.progressCv.wait();
            }
            if (control.hasError)
                throw new Exception(control.errorMsg);
        }
    }

    // Now it is safe to pop the earliest message
    auto addr = getAddr(cur.dest, true);
    auto msg  = control.queues[otherId][id].popFront();
    doAssign(cur, addr, msg.value);
	delay = cur.complexity;
}

	void runStatementArray (AssignStatement cur, CallExpression call)
	{
		auto values = call.argumentList
		    .map !(e => evalExpression (e)).array;

		if (values.length < 1)
		{
			throw new Exception
			    ("array: no first argument");
		}
		if (values[0] < 0)
		{
			throw new Exception ("array: " ~
			    "first argument is " ~ values[0].text);
		}
		if (values.length > 1)
		{
			throw new Exception
			    ("array: more than one argument");
		}

		if (cur.dest.index !is null)
		{
			throw new Exception
			    ("array: destination can not have index");
		}

		foreach_reverse (ref curState; state)
		{
			if (cur.dest.name in curState.arrays)
			{
				curState.arrays[cur.dest.name] =
				    Array (new long [values[0].to !(size_t)]);
				return;
			}
		}
		state.back.arrays[cur.dest.name] =
		    Array (new long [values[0].to !(size_t)]);
	}

	void runStatementImpl (Statement s)
	{
		auto cur0 = cast (AssignStatement) (s);
		if (cur0 !is null) with (cur0)
		{
			// special syntax for receive and array
			auto expr0 = cast (CallExpression) (expr);
			if (expr0 !is null && expr0.name == "receive")
			{
				runStatementReceive (cur0, expr0);
				return;
			}

			if (type == Type.assign &&
			    expr0 !is null && expr0.name == "array")
			{
				runStatementArray (cur0, expr0);
				return;
			}

			auto value = evalExpression (expr);
			auto addr = getAddr (dest, type == Type.assign);
			doAssign (cur0, addr, value);
			delay = complexity;
			return;
		}

		auto cur1 = cast (CallStatement) (s);
		if (cur1 !is null) with (cur1)
		{
			evalCall (call);
			delay = complexity;
			return;
		}

		state ~= Context (s, -1);
	}

	void runStatement (Statement s)
	{
		try
		{
			runStatementImpl (s);
		}
		catch (Exception e)
		{
			throw new Exception (format
			    ("line %s: %s", s.lineId, e.msg));
		}
	}

	bool step ()
	{
		if (delay > 0)
		{
			delay -= 1;
			return true;
		}

		if (state.empty)
		{
			return false;
		}

		with (state.back)
		{
			auto cur0 = cast (FunctionBlock) (parent);
			if (cur0 !is null) with (cur0)
			{
				if (pos < 0)
				{
					pos += 1;
					block = statementList;
					delay = complexity;
				}
				else if (pos >= block.length)
				{
					state.popBack ();
				}
				else
				{
					pos += 1;
					runStatement (block[pos - 1]);
				}
				return true;
			}

			auto cur1 = cast (IfBlock) (parent);
			if (cur1 !is null) with (cur1)
			{
				if (pos < 0)
				{
					auto value = evalExpression (cond);
					block = value ?
					    statementListTrue :
					    statementListFalse;
					pos += 1;
					delay = complexity;
				}
				else if (pos >= block.length)
				{
					state.popBack ();
				}
				else
				{
					pos += 1;
					runStatement (block[pos - 1]);
				}
				return true;
			}

			auto cur2 = cast (WhileBlock) (parent);
			if (cur2 !is null) with (cur2)
			{
				if (pos >= block.length)
				{
					pos = -1;
				}
				if (pos < 0)
				{
					auto value = evalExpression (cond);
					delay = complexity;
					if (value)
					{
						block = statementList;
						pos += 1;
					}
					else
					{
						state.popBack ();
					}
				}
				else
				{
					pos += 1;
					runStatement (block[pos - 1]);
				}
				return true;
			}

			bool hasNext (long value, long finishValue, ForStyle style) {
				final switch (style) {
					case ForStyle.until:
						return value < finishValue;
					case ForStyle.rangeto:
						return value <= finishValue;
					case ForStyle.downto:
						return value >= finishValue;
				}
			}

			void setValueNext (ref long value, ForStyle style) {
				final switch (style) {
					case ForStyle.rangeto:
					case ForStyle.until:
						value += 1;
						break;
					case ForStyle.downto:
						value -= 1;
						break;
				}
			}

			auto cur3 = cast (ForBlock) (parent);
			if (cur3 !is null) with (cur3)
			{
				if (pos < 0)
				{
					block = statementList;
					auto startValue =
					    evalExpression (start);
					auto finishValue =
					    evalExpression (finish);
					vars[name] = Var (startValue);
					delay = complexity;
					delay += 3;
					if (hasNext (vars[name].value, finishValue, style))
					{
						pos += 1;
					}
					else
					{
						state.popBack ();
					}
				}
				else if (pos >= block.length)
				{
					auto finishValue =
					    evalExpression (finish);
					setValueNext (vars[name].value, style);
					delay += 7;
					if (hasNext (vars[name].value, finishValue, style))
					{
						pos = 0;
					}
					else
					{
						state.popBack ();
					}
				}
				else
				{
					pos += 1;
					runStatement (block[pos - 1]);
				}
				return true;
			}

			assert (false);
		}
	}
}

class RunnerControl
{
    Runner[] runners;
    Mailbox[][] queues;              // [from][to]
    shared ulong[] nextMicrotick;     // per thread: next microtick it can execute/send on
    Mutex progressMtx;
    Condition progressCv;

    Mutex printMtx;                  // optional but strongly recommended for print()
    shared bool hasError;
    shared string errorMsg;
	shared long[] ticksDone;
	long lastTicks;

	@property long ticks() const { return lastTicks; }

	private void wakeAllMailboxes()
	{
		foreach (i; 0 .. num)
			foreach (j; 0 .. num)
				queues[i][j].notifyAll();
	}

    @property int num() const
	{
		return runners.length.to !(int);
	}

	this (Args...) (int num_, FunctionBlock p, Args args)
	{
		runners = new Runner [num_];
		foreach (i, ref r; runners)
		{
			r = new Runner(this, i.to!(int), p, args);
		}

		queues = new Mailbox[][](num_, num_);
		foreach (i; 0 .. num_)
		{
			foreach (j; 0 .. num_)
			{
				queues[i][j] = new Mailbox();
			}
		}

		nextMicrotick = new shared ulong[num_];
		foreach (i; 0 .. num_)
		{
			atomicStore(nextMicrotick[i], cast(ulong)i);
		}

		progressMtx = new Mutex;
		progressCv  = new Condition(progressMtx);
		printMtx    = new Mutex;
		hasError    = false;
		errorMsg    = "";

		ticksDone = new shared long[num_];
		foreach (i; 0 .. num_)
			atomicStore(ticksDone[i], 0L);

		lastTicks = 0L;
	}

	bool runParallel (long maxSteps)
	{
		auto group = new ThreadGroup;

		foreach (i; 0 .. num)
		{
			group.create((int idx) {
				return () {
					long calls = 0L;
					scope (exit) atomicStore(ticksDone[idx], calls);

					try
					{
						auto r = runners[idx];

						for (long s = 0L; s < maxSteps; s++)
						{
							if (!r.step())
							{
								atomicStore(nextMicrotick[idx], ulong.max);
								synchronized (progressMtx) { progressCv.notifyAll(); }
								return;
							}

							calls += 1;

							r.microtick += cast(ulong)num;
							atomicStore(nextMicrotick[idx], r.microtick);

							synchronized (progressMtx) { progressCv.notifyAll(); }

							if (hasError) return;
						}
					}
					catch (Throwable e)
					{
						synchronized (progressMtx)
						{
							hasError = true;
							errorMsg = "id " ~ idx.to!string ~ ", " ~ e.toString();
							progressCv.notifyAll();
						}

						atomicStore(nextMicrotick[idx], ulong.max);

						wakeAllMailboxes();
					}
				};
			}(i));
		}

		group.joinAll();

		lastTicks = 0L;
		foreach (i; 0 .. num)
		{
			auto t = atomicLoad(ticksDone[i]);
			if (t > lastTicks) lastTicks = t;
		}

		if (hasError)
			throw new Exception(errorMsg);

		foreach (i; 0 .. num)
		{
			if (atomicLoad(nextMicrotick[i]) != ulong.max)
				return true;
		}
		return false;
	}
}
