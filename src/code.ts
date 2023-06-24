import { exec } from 'child_process';
import fs from 'fs';
import { addToImportFile } from './util';

const skip = false;

export function createCodeFiles(leanPath: string, linesPerPart: number, callback: (funcName: string, constraintsParts: number, witnessParts: number) => void) {
	console.log("Creating code files");
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

function getIRLines(irLines: string[], argIdToName: Map<string, string>): [line: string, nondet: boolean][] {
	let fullLines: [line: string, nondet: boolean][] = [];
	let nondet = false;
	for (let lineIndex = 2; lineIndex < irLines.length; ++lineIndex) {
		const line = irLines[lineIndex];
		if (line.startsWith("%")) {
			const nameEnd = line.indexOf(" ");
			const name = line.slice(0, nameEnd);
			const rhsStart = nameEnd + " = ".length;
			const rhs = line.slice(rhsStart);
			if (rhs.startsWith("cirgen.const ")) {
				const val = line.slice(rhsStart + "cirgen.const ".length);
				fullLines.push([`"${name}" ←ₐ .Const ${val}`, nondet]);
			} else if (rhs.startsWith("cirgen.true")) {
				fullLines.push([`"${name}"←ₐ ⊤`, nondet]);
			} else if (rhs.startsWith("cirgen.get ")) {
				const bufferArg = rhs.slice("cirgen.get ".length, rhs.indexOf("["));
				const offset = rhs.slice(rhs.indexOf("[") + 1, rhs.indexOf("]"));
				const backStart = rhs.indexOf("back ") + "back ".length;
				const backEnd = rhs.indexOf(" ", backStart);
				const back = rhs.slice(backStart, backEnd);
				fullLines.push([`"${name}" ←ₐ .Get ⟨"${argIdToName.get(bufferArg)}"⟩ ${back} ${offset}`, nondet]);
			} else if (rhs.startsWith("cirgen.mul ")) {
				const op1Start = "cirgen.mul ".length;
				const op1End = rhs.indexOf(" ", op1Start);
				const op2Start = rhs.indexOf("%", op1End);
				const op2End = rhs.indexOf(" ", op2Start);
				const op1 = rhs.slice(op1Start, op1End);
				const op2 = rhs.slice(op2Start, op2End);
				fullLines.push([`"${name}" ←ₐ .Mul ⟨"${op1}"⟩ ⟨"${op2}"⟩`, nondet]);
			} else if (rhs.startsWith("cirgen.add ")) {
				const op1Start = "cirgen.add ".length;
				const op1End = rhs.indexOf(" ", op1Start);
				const op2Start = rhs.indexOf("%", op1End);
				const op2End = rhs.indexOf(" ", op2Start);
				const op1 = rhs.slice(op1Start, op1End);
				const op2 = rhs.slice(op2Start, op2End);
				fullLines.push([`"${name}" ←ₐ .Add ⟨"${op1}"⟩ ⟨"${op2}"⟩`, nondet]);
			} else if (rhs.startsWith("cirgen.sub ")) {
				const op1Start = "cirgen.sub ".length;
				const op1End = rhs.indexOf(" ", op1Start);
				const op2Start = rhs.indexOf("%", op1End);
				const op2End = rhs.indexOf(" ", op2Start);
				const op1 = rhs.slice(op1Start, op1End);
				const op2 = rhs.slice(op2Start, op2End);
				fullLines.push([`"${name}" ←ₐ .Sub ⟨"${op1}"⟩ ⟨"${op2}"⟩`, nondet]);
			} else if (rhs.startsWith("cirgen.isz ")) {
				const opStart = rhs.indexOf("%");
				const opEnd = rhs.indexOf(" ", opStart);
				const op = rhs.slice(opStart, opEnd);
				fullLines.push([`"${name}" ←ₐ ??₀⟨"${op}"⟩`, nondet]);
			} else if (rhs.startsWith("cirgen.and_eqz ")) {
				const op1Start = rhs.indexOf("%");
				const op1End = rhs.indexOf(",", op1Start);
				const op2Start = rhs.indexOf("%", op1End);
				const op2End = rhs.indexOf(" ", op2Start);
				const op1 = rhs.slice(op1Start, op1End);
				const op2 = rhs.slice(op2Start, op2End);
				fullLines.push([`"${name}" ←ₐ ⟨"${op1}"⟩ &₀ ⟨"${op2}"⟩`, nondet]);
			} else {
				throw `Unhandled line ${line}`;
			}
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
			const bufferName = argIdToName.get(buffer);
			fullLines.push([`⟨"${bufferName}"⟩[${index}] ←ᵢ ⟨"${val}"⟩`, nondet]);
		} else if (line.startsWith("cirgen.eqz ")) {
			const valStart = line.indexOf("%");
			const valEnd = line.indexOf(" ", valStart);
			const val = line.slice(valStart, valEnd);
			fullLines.push([`?₀ ⟨"${val}"⟩`, nondet]);
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
	return fullLines;
}

function irLinesToLean(lines: [string, boolean][]) {
	const [combinedText, nonDet] = lines.reduce(([acc, accNondet], [line, lineNondet]) => {
		if (accNondet) {
			if (lineNondet) {
				if (acc == "") {
					return [`  nondet (\n    ${line})`, true];
				} else {
					return [`${acc};\n    ${line}`, true];
				}
			} else {
				if (acc == "") {
					return [`  ${line}`, false];
				} else {
					return [`${acc}\n  );\n  ${line}`, false];
				}
			}
		} else {
			if (lineNondet) {
				if (acc == "") {
					return [`  nondet (\n    ${line}`, true];
				} else {
					return [`${acc};\n  nondet (\n    ${line}`, true];
				}
			} else {
				if (acc == "") {
					return [`  ${line}`, false];
				} else {
					return [`${acc};\n  ${line}`, false];
				}
			}
		}
	}, ["", false]);
	if (nonDet) {
		return `${combinedText}\n  )`;
	} else {
		return combinedText;
	}
}

function irLinesToParts(lines: [string, boolean][], linesPerPart: number): string {
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
					`  st.props[(⟨"${op}"⟩: PropVar)].get!`
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

function partsCombine(fullLines: [string, boolean][], linesPerPart: number): string {
	let tactics: string[] = [];
	for (let part = 0; part * linesPerPart < fullLines.length; ++part) {
		tactics.push(`  unfold part${part}`);
		if ((part + 1) * linesPerPart >= fullLines.length) {
			tactics.push(`  rfl`)
		} else {
			for (let i = 0; i < linesPerPart && part * linesPerPart + i < fullLines.length; ++i) {
				const [_, nondet] = fullLines[part * linesPerPart + i];
				if (!nondet) {
					if (i == linesPerPart - 1) {
						tactics.push(`  apply MLIR.seq_step_eq\n  intro st`)
					} else {
						tactics.push(`  apply MLIR.nested_seq_step_eq\n  intro st`);
					}
				} else {
					// TODO range check this
					const [_, nextNondet] = fullLines[part * linesPerPart + i + 1]
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
	const witnessFullLines = getIRLines(witness, argIdToName);
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
	const constraintsFullLines = getIRLines(constraints, argIdToName);
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