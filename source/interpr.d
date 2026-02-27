// Author: Ivan Kazmenko (gassa@mail.ru)
module interpr;
import std.algorithm;
import std.conv;
import std.exception;
import std.range;
import std.stdio;
import std.string;
import display;
import language;
import parser;
import runner;

int main (string [] args)
{
	// set default parameters
	bool compileOnly = false;
	bool doDisplay = false;
	int num = 100;
	long steps = 1_000_000L;
	string fileName = "";

	// read custom parameters from arguments
	int pos = 1;
	while (pos < args.length)
	{
		if (args[pos] == "-c")
		{
			compileOnly = true;
		}
		else if (args[pos] == "-d")
		{
			doDisplay = true;
		}
		else if (args[pos] == "-n")
		{
			pos += 1;
			num = args[pos].to !(int);
		}
		else if (args[pos] == "-s")
		{
			pos += 1;
			steps = args[pos].to!(long);
		}
		else
		{
			fileName = args[pos];
		}
		pos += 1;
	}

	// compile program
	auto f = File (fileName, "rt");
	auto s = new StatementParser ();
	FunctionBlock p;
	try
	{
		p = s.parse (f.byLineCopy.array);
	}
	catch (Exception e)
	{
		stderr.writeln (e.msg);
		return 1;
	}
	if (doDisplay)
	{
		displayFunction (p);
	}
	if (compileOnly)
	{
		return 0;
	}

	// read input
	auto n = readln.strip.to !(long);
	auto a = readln.splitter.map !(to !(long)).array;

	// execute program
	auto rc = new RunnerControl (num, p, n, a);
	long step = 0;
	bool working = true;

	try
	{
		working = rc.runParallel(steps);
		step = rc.ticks;
	}
	catch (Exception e)
	{
		stderr.writeln("step ", rc.ticks, ", ", e.msg);
		return 1;
	}

	stderr.writeln("steps: ", step);

	// simulate time limit exceeded
	if (working)
	{
		for (ulong i = 0; ; i++)
		{
		}
	}

	return 0;
}
