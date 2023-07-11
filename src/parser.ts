import * as IR from './IR';

export function parseBody(mlir: string[], argIdToName: Map<string, string>): IR.Statement[] {
	const body = mlir.slice(2);
	let nondet = false;
	const scopes: [IR.Statement[], string][] = [[[], "module"]];
	for (let lineIndex = 0; lineIndex < body.length; ++lineIndex) {
		const line = body[lineIndex].trim();
		const instructions = scopes[scopes.length-1][0];

		if (line.startsWith("%")) {
			instructions.push(parseAssign(line, nondet, argIdToName));
		} else if (line.startsWith("cirgen.nondet ")) {
			nondet = true;
			scopes.push([[], "nondet"]);
		} else if (line.startsWith("cirgen.set ")) {
			instructions.push(parseSet(line, nondet, argIdToName));
		} else if (line.startsWith("cirgen.if ")) {
			const valStart = line.indexOf("%");
			const valEnd = line.indexOf(" ", valStart);
			const val = line.slice(valStart, valEnd);
			scopes.push([[], val]);
		} else if (line.startsWith("cirgen.eqz ")) {
			const valStart = line.indexOf("%");
			const valEnd = line.indexOf(" ", valStart);
			const val = line.slice(valStart, valEnd);
			instructions.push(new IR.Eqz(val, nondet));
		} else if (line.startsWith("cirgen.barrier ")) {
			// skip barrier
		} else if (line === "}") {
			const scopeTag = scopes[scopes.length-1][1];
			if (scopeTag === "module") throw "Did not find return when parsing MLIR";

			const outerScope = scopes[scopes.length-2][0];
			if (scopeTag === "nondet") {
				outerScope.push(...instructions);
				nondet = false;
			} else { // scope is an if, string is its value
				outerScope.push(new IR.If(scopeTag, instructions, nondet));
			}
			scopes.pop();
		} else if (line === "return" || line.startsWith("return ")) {
			break;
		} else {
			throw `Unhandled line ${line}`;
		}
	}
	if (scopes.length > 1) {
		throw "Returns in nested scopes not implemented yet";
	}
	return scopes[0][0];
}

function parseSet(line: string, nondet: boolean, argIdToName: Map<string, string>): IR.SetInstr {
	const bufferStart = line.indexOf("%");
	const bufferEnd = line.indexOf(" ", bufferStart);
	const indexStart = line.indexOf("[") + 1;
	const indexEnd = line.indexOf("]");
	const valStart = line.indexOf("%", indexEnd);
	const valEnd = line.indexOf(" ", valStart);
	const buffer = line.slice(bufferStart, bufferEnd);
	const index = line.slice(indexStart, indexEnd);
	const val = line.slice(valStart, valEnd);
	const bufferName = `${argIdToName.get(buffer)}`;
	return new IR.SetInstr(bufferName, index, val, nondet);
}

function parseAssign(line: string, nondet: boolean, argIdToName: Map<string, string>): IR.Assign {
	const nameEnd = line.indexOf(" ");
	const name = line.slice(0, nameEnd);
	const rhsStart = nameEnd + " = ".length;
	const rhs = line.slice(rhsStart);
	let rhsVal: IR.Val | undefined;
	if (rhs.startsWith("cirgen.const ")) {
		const val = line.slice(rhsStart + "cirgen.const ".length);
		rhsVal = new IR.Const(val);
	} else if (rhs.startsWith("cirgen.true")) {
		rhsVal = new IR.True();
	} else if (rhs.startsWith("cirgen.get ")) {
		const bufferArg = rhs.slice("cirgen.get ".length, rhs.indexOf("["));
		const offset = rhs.slice(rhs.indexOf("[") + 1, rhs.indexOf("]"));
		const backStart = rhs.indexOf("back ") + "back ".length;
		const backEnd = rhs.indexOf(" ", backStart);
		const back = rhs.slice(backStart, backEnd);
		rhsVal = new IR.Get(`${argIdToName.get(bufferArg)}`, back, offset);
	} else if (rhs.startsWith("cirgen.mul ")) {
		const op1Start = "cirgen.mul ".length;
		const op1End = rhs.indexOf(" ", op1Start);
		const op2Start = rhs.indexOf("%", op1End);
		const op2End = rhs.indexOf(" ", op2Start);
		const op1 = rhs.slice(op1Start, op1End);
		const op2 = rhs.slice(op2Start, op2End);
		rhsVal = new IR.BinOp("Mul", op1, op2);
	} else if (rhs.startsWith("cirgen.add ")) {
		const op1Start = "cirgen.add ".length;
		const op1End = rhs.indexOf(" ", op1Start);
		const op2Start = rhs.indexOf("%", op1End);
		const op2End = rhs.indexOf(" ", op2Start);
		const op1 = rhs.slice(op1Start, op1End);
		const op2 = rhs.slice(op2Start, op2End);
		rhsVal = new IR.BinOp("Add", op1, op2);
	} else if (rhs.startsWith("cirgen.sub ")) {
		const op1Start = "cirgen.sub ".length;
		const op1End = rhs.indexOf(" ", op1Start);
		const op2Start = rhs.indexOf("%", op1End);
		const op2End = rhs.indexOf(" ", op2Start);
		const op1 = rhs.slice(op1Start, op1End);
		const op2 = rhs.slice(op2Start, op2End);
		rhsVal = new IR.BinOp("Sub", op1, op2);
	} else if (rhs.startsWith("cirgen.inv ")) {
		const opStart = rhs.indexOf("%");
		const opEnd = rhs.indexOf(" ", opStart);
		const op = rhs.slice(opStart, opEnd);
		rhsVal = new IR.Inv(op);
	} else if (rhs.startsWith("cirgen.isz ")) {
		const opStart = rhs.indexOf("%");
		const opEnd = rhs.indexOf(" ", opStart);
		const op = rhs.slice(opStart, opEnd);
		rhsVal = new IR.IsZ(op);
	} else if (rhs.startsWith("cirgen.and_eqz ")) {
		const op1Start = rhs.indexOf("%");
		const op1End = rhs.indexOf(",", op1Start);
		const op2Start = rhs.indexOf("%", op1End);
		const op2End = rhs.indexOf(" ", op2Start);
		const op1 = rhs.slice(op1Start, op1End);
		const op2 = rhs.slice(op2Start, op2End);
		rhsVal = new IR.AndEqz(op1, op2);
	} else if (rhs.startsWith("cirgen.bitAnd ")) {
		const op1Start = rhs.indexOf("%");
		const op1End = rhs.indexOf(" ", op1Start);
		const op2Start = rhs.indexOf("%", op1End);
		const op2End = rhs.indexOf(" ", op2Start);
		const op1 = rhs.slice(op1Start, op1End);
		const op2 = rhs.slice(op2Start, op2End);
		rhsVal = new IR.BinOp("BitAnd", op1, op2);
	} else if (rhs.startsWith("cirgen.and_cond ")) {
		const outerStart = rhs.indexOf("%");
		const outerEnd = rhs.indexOf(",", outerStart);
		const outerConstraint = rhs.slice(outerStart, outerEnd);
		const condStart = rhs.indexOf("%", outerEnd);
		const condEnd = rhs.indexOf(" ", condStart);
		const condition = rhs.slice(condStart, condEnd);
		const innerStart = rhs.indexOf("%", condEnd);
		const innerConstraint = rhs.slice(innerStart);
		rhsVal = new IR.AndCond(outerConstraint, condition, innerConstraint);
	} else {
		throw `Unhandled line ${line}`;
	}

	return new IR.Assign(name, rhsVal, nondet);
}
