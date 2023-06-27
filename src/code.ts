import { exec } from 'child_process';
import fs from 'fs';
import { addToImportFile } from './util';
import { IR } from './IR';

const skip = false;

export function createCodeFiles(leanPath: string, linesPerPart: number, callback: (funcName: string, constraintsParts: number, witnessParts: number) => void) {
	console.log(`Creating code files ${skip ? "skipped" : ""}`);
	const witness = loadWitnessMLIR();
	const constraints = loadConstraintsMLIR();
	const [funcName, args, argIdToName] = parseFuncLine(witness[1]);

	const [witnessCodeLean, witnessPartCount] = createWitnessCodeLean(funcName, witness, argIdToName, linesPerPart);
	const [constraintsCodeLean, constraintsPartCount] = createConstraintsCodeLean(funcName, constraints, argIdToName, linesPerPart);
	if (skip) {
		callback(funcName, constraintsPartCount, witnessPartCount);
	} else {
		outputCodeFiles(leanPath, funcName, witnessCodeLean, constraintsCodeLean);
	
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			if (stdout !== "") {
				console.log("---stdout---:\n\n");
				console.log(stdout);
			}
			if (stderr !== "") {
				console.log("---stderr:\n\n");
				console.log(stderr);
			}
			if (error !== null) {
				console.log("---error---:\n\n");
				console.log(error);
			} else {
				callback(funcName, constraintsPartCount, witnessPartCount);
			}
		})
	}
}

function loadWitnessMLIR(): string[] {
	// witness code as array of lines
	return fs.readFileSync("./witness.txt", { encoding: "utf8" })
		.split("\n")
		.map(line => line.trim());
}

function loadConstraintsMLIR(): string[] {
	// constraints code as array of lines
	return fs.readFileSync("./constraints.txt", { encoding: "utf8" })
		.split("\n")
		.map(line => line.trim());
}

type Arg = {
	id: string;
	width: number;
	name: string;
};
function parseFuncLine(funcLine: string): [string, Arg[], Map<string, string>] {
	//Get name
	const funcNameEnd = funcLine.indexOf("(");
	const funcName = funcLine.slice("func.func @".length, funcNameEnd);

	//Get arguments

	const argsLine = funcLine.slice(funcLine.indexOf("(") + 1, funcLine.lastIndexOf(")"));
	let index = 0;
	let args: Arg[] = [];
	let argIdToName = new Map<string, string>();
	while (index < argsLine.length) {
		const argNameEnd = argsLine.indexOf(":", index);
		const argName = argsLine.slice(index, argNameEnd);
		const widthStart = argsLine.indexOf("<", index) + 1;
		const widthEnd = argsLine.indexOf(",", index);
		const width = argsLine.slice(widthStart, widthEnd);
		const nameStart = argsLine.indexOf("\"", index) + 1;
		const nameEnd = argsLine.indexOf("\"", nameStart);
		const name = argsLine.slice(nameStart, nameEnd);
		index = nameEnd + "\"}, ".length;
		args.push({ id: argName, width: parseInt(width), name });
		argIdToName.set(argName, name);
	}
	return [funcName, args, argIdToName];
}

function parseIRLines(irLines: string[], argIdToName: Map<string, string>): IR.Statement[] {
	let instructions: IR.Statement[] = [];
	let nondet = false;
	for (let lineIndex = 2; lineIndex < irLines.length; ++lineIndex) {
		const line = irLines[lineIndex];
		if (line.startsWith("%")) {
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
			} else {
				throw `Unhandled line ${line}`;
			}
			instructions.push(new IR.Assign(name, rhsVal, nondet));
		} else if (line.startsWith("cirgen.nondet ")) {
			nondet = true;
		} else if (line.startsWith("cirgen.set ")) {
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
			instructions.push(new IR.SetInstr(bufferName, index, val, nondet));
		} else if (line.startsWith("cirgen.eqz ")) {
			const valStart = line.indexOf("%");
			const valEnd = line.indexOf(" ", valStart);
			const val = line.slice(valStart, valEnd);
			instructions.push(new IR.Eqz(val, nondet));
		} else if (line.startsWith("}") && nondet == true) {
			nondet = false;
		} else if (line.startsWith("cirgen.barrier ")) {
			// skip barrier
		} else if (line == "return" || line.startsWith("return ")) {
			break;
		} else {
			throw `Unhandled line ${line}`;
		}
	}
	return instructions;
}

function irLinesToLean(ir: IR.Statement[]): string {
	let nondet = false;
	let res = "";
	for (let i = 0; i < ir.length; ++i) {
		//Add the continuation between the previous statement and this
		if (ir[i].nondet && !nondet) {
			if (i == 0) {
				res = "  nondet (\n    ";
			} else {
				res = `${res};\n  nondet (\n    `;
			}
			nondet = true;
		} else if (!ir[i].nondet && nondet) {
			res = `${res}\n  );\n  `;
			nondet = false;
		} else if (i == 0) {
			res = "  ";
		} else if (nondet) {
			res = `${res};\n    `;
		} else {
			res = `${res};\n  `;
		}

		//Add the current statement
		res = `${res}${ir[i].toString()}`

		if (i == ir.length - 1 && nondet) {
			res = `${res}\n  )`
		}
	}
	return res;
}

function irLinesToParts(lines: IR.Statement[], linesPerPart: number): string {
	let output: string[] = [];
	for (let i = 0; i * linesPerPart < lines.length; ++i) {
		output.push(`def part${i} : MLIRProgram :=`);
		output.push(irLinesToLean(lines.slice(i * linesPerPart, (i + 1) * linesPerPart)));
	}
	return output.join("\n");
}

function getWitnessReturn(witnessCode: string[]): string {
	return [
		"def getReturn (st: State) : BufferAtTime :=",
		"  st.buffers ⟨\"data\"⟩ |>.get!.getLast!",
		// TODO generalise to not just the single specific buffer
	].join("\n");
}

function getConstraintsReturn(constraintsCode: string[]): string {
	return constraintsCode
		.map(line => {
			if (line.startsWith("return ")) {
				const opStart = line.indexOf("%");
				const opEnd = line.indexOf(" ", opStart);
				const op = line.slice(opStart, opEnd);
				return [
					"def getReturn (st: State) : Prop :=",
					`  st.constraintsInVar ⟨"${op}"⟩`
				].join("\n");
			} else {
				return "";
			}
		})
		.filter(line => line !== "")
	[0];
}

function parts(length: number, linesPerPart: number): string[] {
	const numParts = Math.ceil(length / linesPerPart);
	let output = [];
	for (let i = 0; i < numParts; ++i) output.push(i);
	return output.map(i => `part${i}`);
}

function partsCombine(fullLines: IR.Statement[], linesPerPart: number): string {
	let tactics: string[] = [];
	for (let part = 0; part * linesPerPart < fullLines.length; ++part) {
		tactics.push(`  unfold part${part}`);
		if ((part + 1) * linesPerPart >= fullLines.length) {
			tactics.push(`  rfl`)
		} else {
			for (let i = 0; i < linesPerPart && part * linesPerPart + i < fullLines.length; ++i) {
				const nondet = fullLines[part * linesPerPart + i].nondet;
				if (!nondet) {
					if (i == linesPerPart - 1) {
						tactics.push(`  apply MLIR.seq_step_eq\n  intro st`)
					} else {
						tactics.push(`  apply MLIR.nested_seq_step_eq\n  intro st`);
					}
				} else {
					// TODO range check this
					const nextNondet = fullLines[part * linesPerPart + i + 1].nondet
					if (nextNondet) { // nondet s1; s2 = nondet (s1; s3); s4
						if (i == linesPerPart - 1) {
							tactics.push(`  apply MLIR.nondet_step_eq\n  intro st`)
						} else { // nondet (s1; s2); s3 = nondet (s1; s4); s5
							tactics.push(`  apply MLIR.nondet_seq_step_eq\n  intro st`)
						}
					} else {
						if (i == linesPerPart - 1) { // nondet s1; s2 = nondet s1; s3
							tactics.push(`  apply MLIR.seq_step_eq\n  intro st`)
						} else { // (nondet s1; s2); s3 = nondet s1; s4
							tactics.push(`  apply MLIR.nondet_end_step_eq\n  intro st`)
						}
					}
				}
			}
		}
	}
	return [
		"lemma parts_combine {st: State} :",
		"  Γ st ⟦parts_combined⟧ =",
		"  Γ st ⟦full⟧ := by",
		"  unfold full parts_combined",
		...tactics
	].join("\n");
}

function createWitnessCodeLean(funcName: string, witness: string[], argIdToName: Map<string, string>, linesPerPart: number): [string, number] {
	const witnessFullLines = parseIRLines(witness, argIdToName);
	return [[
		"import Risc0.Basic",
		"import Risc0.Lemmas",
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"",
		"def full : MLIRProgram :=",
		irLinesToLean(witnessFullLines),
		getWitnessReturn(witness),
		"def run (st: State) : BufferAtTime :=",
		"  getReturn (full.runProgram st)",
		irLinesToParts(witnessFullLines, linesPerPart),
		"",
		"abbrev parts_combined : MLIRProgram :=",
		`  ${parts(witnessFullLines.length, linesPerPart).join("; ")}`,
		partsCombine(witnessFullLines, linesPerPart),
		"",
		`end Risc0.${funcName}.Witness.Code`,
		""
	].join("\n"), Math.ceil(witnessFullLines.length / linesPerPart)];
}

function createConstraintsCodeLean(funcName: string, constraints: string[], argIdToName: Map<string, string>, linesPerPart: number): [string, number] {
	const constraintsFullLines = parseIRLines(constraints, argIdToName);
	return [[
		"import Risc0.Basic",
		"import Risc0.Lemmas",
		"",
		`namespace Risc0.${funcName}.Constraints.Code`,
		"",
		"open MLIRNotation",
		"",
		"def full : MLIRProgram :=",
		irLinesToLean(constraintsFullLines),
		getConstraintsReturn(constraints),
		"def run (st: State) : Prop :=",
		"  getReturn (full.runProgram st)",
		irLinesToParts(constraintsFullLines, linesPerPart),
		"",
		"abbrev parts_combined : MLIRProgram :=",
		`  ${parts(constraintsFullLines.length, linesPerPart).join("; ")}`,
		"lemma parts_combine {st: State} :",
		"  Γ st ⟦parts_combined⟧ =",
		"  Γ st ⟦full⟧ := by",
		"  unfold full parts_combined",
		`    ${parts(constraintsFullLines.length, linesPerPart).join(" ")}`,
		"  simp [MLIR.seq_assoc, MLIR.run_seq_def]",
		"",
		`end Risc0.${funcName}.Constraints.Code`,
		""
	].join("\n"), Math.ceil(constraintsFullLines.length / linesPerPart)];
}

function outputCodeFiles(prefix: string, funcName: string, witnessCodeLean: string, constraintsCodeLean: string) {
	mkDirIfNeeded(`${prefix}/Risc0/Gadgets/${funcName}`);
	mkDirIfNeeded(`${prefix}/Risc0/Gadgets/${funcName}/Witness`);
	mkDirIfNeeded(`${prefix}/Risc0/Gadgets/${funcName}/Constraints`);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Witness/Code.lean`, witnessCodeLean);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Constraints/Code.lean`, constraintsCodeLean);

	addToImportFile(prefix, `${funcName}.Witness.Code`);
	addToImportFile(prefix, `${funcName}.Constraints.Code`);
}

function mkDirIfNeeded(path: string) {
	if (!fs.existsSync(path)) {
		fs.mkdirSync(path);
	}
}