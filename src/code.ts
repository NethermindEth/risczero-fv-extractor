import { exec } from 'child_process';
import fs from 'fs';
import { addToImportFile } from './util';
import { IR, irLinesToLean, irLinesToParts, parts } from './IR';
import { delayConstsAndGets, getDelayProof, getStepwiseOptimisations } from './reordering';
import { createWitnessCodeWithDropsLean, createCodeDropsLean } from './drops';
import { createCodePartsLean } from './code_parts';

const skipUnOpt = false;
const skipOpt = false;

export function createCodeFiles(
	leanPath: string,
	linesPerPart: number,
	callback: (funcName: string, constraintsReorderedIR: IR.Statement[], constraintsPartDrops: IR.DropFelt[][], witnessReorderedIR: IR.Statement[], witnessPartDrops: IR.DropFelt[][]) => void
) {
	console.log(`Creating code files ${skipUnOpt ? "unopt skipped" : ""} ${skipOpt ? "opt skipped" : ""}`);
	const witness = loadWitnessMLIR();
	const constraints = loadConstraintsMLIR();
	const [funcName, args, argIdToName] = parseFuncLine(witness[1]);

	const witnessCodeLean = createWitnessCodeLean(funcName, witness, argIdToName, linesPerPart);
	const constraintsCodeLean = createConstraintsCodeLean(funcName, constraints, argIdToName, linesPerPart);

	const [witnessReorderedIR, witnessReorderedLean] = createWitnessCodeReorderedLean(funcName, witness, argIdToName, linesPerPart);
	const [constraintsReorderedIR, constraintsReorderedLean] = createConstraintsCodeReorderedLean(funcName, constraints, argIdToName, linesPerPart);

	const witnessPartsLean = createCodePartsLean(funcName, witnessReorderedIR, linesPerPart, "Witness");
	const constraintsPartsLean = createCodePartsLean(funcName, constraintsReorderedIR, linesPerPart, "Constraints");

	const [witnessDropsLean, witnessPartDrops] = createCodeDropsLean(funcName, witnessReorderedIR, linesPerPart, "Witness");
	const [constraintsDropsLean, constraintsPartDrops] = createCodeDropsLean(funcName, constraintsReorderedIR, linesPerPart, "Constraints");

	if (!skipUnOpt) {
		outputCodeFiles(leanPath, funcName, witnessCodeLean, constraintsCodeLean);
	}
	if (!skipOpt) {
		outputOptCodeFiles(
			leanPath, funcName,
			witnessReorderedLean, witnessPartsLean, witnessDropsLean,
			constraintsReorderedLean, constraintsPartsLean, constraintsDropsLean
		);
	}
	if (skipUnOpt && skipOpt) {
		callback(funcName, constraintsReorderedIR, constraintsPartDrops, witnessReorderedIR, witnessPartDrops);
	} else {
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
				callback(funcName, constraintsReorderedIR, constraintsPartDrops, witnessReorderedIR, witnessPartDrops);
			}
		}).stdout?.pipe(process.stdout);
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

function createWitnessCodeLean(funcName: string, witness: string[], argIdToName: Map<string, string>, linesPerPart: number): string {
	const witnessFullLines = parseIRLines(witness, argIdToName);
	return [
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
		"",
		"end Code",
		"",
		// TODO generalize start state
		`def start_state (input : BufferAtTime) : State :=`,
		`  { buffers := Map.fromList [(⟨"in"⟩, [input]), (⟨"data"⟩, [[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]])]`,
		`  , bufferWidths := Map.fromList [(⟨"in"⟩, 4), (⟨"data"⟩, 18)] --input width 128?`,
		`  , constraints := []`,
		`  , cycle := 0`,
		`  , felts := Map.empty`,
		`  , props := Map.empty`,
		`  , vars := [⟨"in"⟩, ⟨"data"⟩]`,
		`  , isFailed := false`,
		`  }`,
		"",
		`end Risc0.${funcName}.Witness`,
		""
	].join("\n");
}

function createConstraintsCodeLean(funcName: string, constraints: string[], argIdToName: Map<string, string>, linesPerPart: number): string {
	const constraintsFullLines = parseIRLines(constraints, argIdToName);
	return [
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
		"",
		"end Code",
		"",
		// TODO generalize start state
		`def start_state (input data : BufferAtTime) : State :=`,
		`  { buffers := Map.fromList [(⟨"in"⟩, [input]), (⟨"data"⟩, [data])]`,
		`  , bufferWidths := Map.fromList [(⟨"in"⟩, 4), (⟨"data"⟩, 18)] --input width 128?`,
		`  , constraints := []`,
		`  , cycle := 0`,
		`  , felts := Map.empty`,
		`  , props := Map.empty`,
		`  , vars := [⟨"in"⟩, ⟨"data"⟩]`,
		`  , isFailed := false`,
		`  }`,
		"",
		`end Risc0.${funcName}.Constraints`,
		""
	].join("\n");
}

function createConstraintsCodeReorderedLean(funcName: string, witness: string[], argIdToName: Map<string, string>, linesPerPart: number): [ir: IR.Statement[], lean: string] {
	const IR = parseIRLines(witness, argIdToName);
	const [reorderedIR, reorderedLean] = getStepwiseOptimisations(IR, linesPerPart);
	IR.forEach(x => console.log(x.toString()));
	return [
		reorderedIR,
		[
			"import Risc0.Map",
			"import Risc0.MlirTactics",
			"import Risc0.Optimisation",
			`import Risc0.Gadgets.${funcName}.Constraints.Code`,
			"",
			`namespace Risc0.${funcName}.Constraints.Code`,
			"",
			"open MLIRNotation",
			reorderedLean,
			"end Risc0.ComputeDecode.Constraints.Code",
		].join("\n")
	];
}

function createWitnessCodeReorderedLean(funcName: string, witness: string[], argIdToName: Map<string, string>, linesPerPart: number): [ir: IR.Statement[], lean: string] {
	const IR = parseIRLines(witness, argIdToName);
	const [reorderedIR, reorderedLean] = getStepwiseOptimisations(IR, linesPerPart);
	IR.forEach(x => console.log(x.toString()));
	return [
		reorderedIR,
		[
			"import Risc0.Map",
			"import Risc0.MlirTactics",
			"import Risc0.Optimisation",
			`import Risc0.Gadgets.${funcName}.Witness.Code`,
			"",
			`namespace Risc0.${funcName}.Witness.Code`,
			"",
			"open MLIRNotation",
			reorderedLean,
			"end Risc0.ComputeDecode.Witness.Code",
		].join("\n")
	];
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

function outputOptCodeFiles(
	prefix: string, funcName: string,
	witnessReordered: string, witnessParts: string, witnessOptimised: string,
	constraintsReordered: string, constraintsParts: string, constraintsOptimised: string
) {
	mkDirIfNeeded(`${prefix}/Risc0/Gadgets/${funcName}`);
	mkDirIfNeeded(`${prefix}/Risc0/Gadgets/${funcName}/Witness`);
	mkDirIfNeeded(`${prefix}/Risc0/Gadgets/${funcName}/Constraints`);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Witness/CodeReordered.lean`, witnessReordered);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Constraints/CodeReordered.lean`, constraintsReordered);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Witness/CodeParts.lean`, witnessParts);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Constraints/CodeParts.lean`, constraintsParts);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Witness/CodeDrops.lean`, witnessOptimised);
	fs.writeFileSync(`${prefix}/Risc0/Gadgets/${funcName}/Constraints/CodeDrops.lean`, constraintsOptimised);

	addToImportFile(prefix, `${funcName}.Constraints.CodeReordered`);
	addToImportFile(prefix, `${funcName}.Witness.CodeReordered`);
	addToImportFile(prefix, `${funcName}.Constraints.CodeParts`);
	addToImportFile(prefix, `${funcName}.Witness.CodeParts`);
	addToImportFile(prefix, `${funcName}.Constraints.CodeDrops`);
	addToImportFile(prefix, `${funcName}.Witness.CodeDrops`);
}

function mkDirIfNeeded(path: string) {
	if (!fs.existsSync(path)) {
		fs.mkdirSync(path);
	}
}