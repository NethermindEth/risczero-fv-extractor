import { exec } from 'child_process';
import fs from 'fs';
import { BufferConfig, addToImportFile, commentInImportFile } from './util';
import * as IR from './IR';
import { getStepwiseOptimisations } from './reordering';
import { createCodeDropsLean } from './drops';
import { createCodePartsLean } from './code_parts';
import { parseBody } from './parser';

const skipUnOpt = false;
const skipOpt = false;

export function createCodeFiles(
	gadgetName: string,
	leanPath: string,
	linesPerPart: number,
	autoExcludeFiles: boolean,
	callback: (funcName: string, bufferConfig: BufferConfig, constraintsReorderedIR: IR.Statement[], constraintsPartDrops: IR.DropFelt[][], witnessReorderedIR: IR.Statement[], witnessPartDrops: IR.DropFelt[][], proofFiles: string[]) => void
) {
	console.log(`Creating code files ${skipUnOpt ? "unopt skipped" : ""} ${skipOpt ? "opt skipped" : ""}`);
	const witness = loadWitnessMLIR(gadgetName);
	const constraints = loadConstraintsMLIR(gadgetName);
	const [funcName, argIdToName, bufferConfig] = parseFuncLine(witness[1]);

	const witnessCodeLean = createWitnessCodeLean(funcName, witness, argIdToName, linesPerPart, bufferConfig);
	const constraintsCodeLean = createConstraintsCodeLean(funcName, constraints, argIdToName, linesPerPart, bufferConfig);

	const [witnessReorderedIR, witnessReorderedLean] = createWitnessCodeReorderedLean(funcName, witness, argIdToName);
	const [constraintsReorderedIR, constraintsReorderedLean] = createConstraintsCodeReorderedLean(funcName, constraints, argIdToName);

	const witnessPartsLean = createCodePartsLean(funcName, witnessReorderedIR, linesPerPart, "Witness");
	const constraintsPartsLean = createCodePartsLean(funcName, constraintsReorderedIR, linesPerPart, "Constraints");

	const [witnessDropsLean, witnessPartDrops] = createCodeDropsLean(funcName, witnessReorderedIR, linesPerPart, "Witness", bufferConfig);
	const [constraintsDropsLean, constraintsPartDrops] = createCodeDropsLean(funcName, constraintsReorderedIR, linesPerPart, "Constraints", bufferConfig);

	let proofFiles: string[];
	if (autoExcludeFiles) {
		proofFiles = excludeFiles(leanPath, funcName);
	} else {
		proofFiles = [];
	}

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
		callback(funcName, bufferConfig, constraintsReorderedIR, constraintsPartDrops, witnessReorderedIR, witnessPartDrops, proofFiles);
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
				callback(funcName, bufferConfig, constraintsReorderedIR, constraintsPartDrops, witnessReorderedIR, witnessPartDrops, proofFiles);
			}
		}).stdout?.pipe(process.stdout);
	}
}

function loadWitnessMLIR(name: string): string[] {
	// witness code as array of lines
	return fs.readFileSync(`./witness-${name}.txt`, { encoding: "utf8" })
		.split("\n")
		.map(line => line.trim());
}

function loadConstraintsMLIR(name: string): string[] {
	// constraints code as array of lines
	return fs.readFileSync(`./constraints-${name}.txt`, { encoding: "utf8" })
		.split("\n")
		.map(line => line.trim());
}

type Arg = {
	id: string;
	width: number;
	name: string;
	mutability: string;
};
function parseFuncLine(funcLine: string): [string, Map<string, string>, BufferConfig] {
	//Get name
	const funcNameEnd = funcLine.indexOf("(");
	const funcName = funcLine.slice("func.func @".length, funcNameEnd);

	//Get arguments

	const argsLine = funcLine.slice(funcLine.indexOf("(") + 1, funcLine.lastIndexOf(")"));
	let index = 0;
	const args: Arg[] = [];
	const argIdToName = new Map<string, string>();
	while (index < argsLine.length) {
		const argNameEnd = argsLine.indexOf(":", index);
		const argName = argsLine.slice(index, argNameEnd);
		const widthStart = argsLine.indexOf("<", index) + 1;
		const widthEnd = argsLine.indexOf(",", index);
		const width = argsLine.slice(widthStart, widthEnd);
		const mutabilityStart = widthEnd+2;
		const mutabilityEnd = argsLine.indexOf(">", mutabilityStart);
		const mutability = argsLine.slice(mutabilityStart, mutabilityEnd);
		const nameStart = argsLine.indexOf("\"", index) + 1;
		const nameEnd = argsLine.indexOf("\"", nameStart);
		const name = argsLine.slice(nameStart, nameEnd);
		index = nameEnd + "\"}, ".length;
		args.push({ id: argName, width: parseInt(width), name, mutability });
		argIdToName.set(argName, name);
	}

	// let inputName: string|null = null;
	// let inputWidth: number|null = null;
	// let outputName: string|null = null;
	// let outputWidth: number|null = null;
	let inputBuffers: [string, number][] = [];
	let outputBuffers: [string, number][] = [];
	for (let i = 0; i < args.length; ++i) {
		if (args[i].mutability === "constant") {
			inputBuffers.push([args[i].name, args[i].width]);
		} else if (args[i].mutability === "mutable") {
			outputBuffers.push([args[i].name, args[i].width]);
		} else {
			throw `Unhandled buffer kind ${args[i].mutability}`;
		}
	}

	return [funcName, argIdToName, {inputs: inputBuffers, outputs: outputBuffers}];
}

function getWitnessReturn(witnessCode: string[], bufferConfig: BufferConfig): string {
	return [
		// "def getReturn (st: State) (res: BufferAtTime) :=",
		`def getReturn (st: State) ${bufferConfig.outputs.map(([name, _]) => `(res_${name}: BufferAtTime)`).join(" ")} : Prop :=`,
		// `  (st.buffers ⟨"${bufferConfig.outputName}"⟩ |>.get!.getLast!) = res`,
		`${bufferConfig.outputs.map(([name, _]) => `  ((st.buffers ⟨"${name}"⟩ |>.get!.getLast!) = res_${name})`).join("∧\n")}`,
                `∧ ¬ st.isFailed`
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
		.filter(line => line !== "")[0];
}

function createWitnessCodeLean(funcName: string, witness: string[], argIdToName: Map<string, string>, linesPerPart: number, bufferConfig: BufferConfig): string {
	const witnessFullLines = parseBody(witness, argIdToName);
	const startStateInputs = bufferConfig.inputs.map(([name, _]) => `(input_${name}: BufferAtTime)`).join(" ");
	const startStateBuffers = [
		...bufferConfig.inputs.map(([name, _]) => `(⟨"${name}"⟩, [input_${name}])`),
		...bufferConfig.outputs.map(([name, width]) => `(⟨"${name}"⟩, [[${Array(width).fill(".none").join(", ")}]])`)
	].join(", ");
	const startStateBufferWidths = [
		...bufferConfig.inputs.map(([name, width]) => `(⟨"${name}"⟩, ${width})`),
		...bufferConfig.outputs.map(([name, width]) => `(⟨"${name}"⟩, ${width})`)
	].join(", ");
	const startStateBufferVars = [
		...bufferConfig.inputs.map(([name, _]) => `⟨"${name}"⟩`),
		...bufferConfig.outputs.map(([name, _]) => `⟨"${name}"⟩`)
	].join(", ");
	const runReturnParams = bufferConfig.outputs.map(([name, _]) => `(res_${name}: BufferAtTime)`).join(" ");
	const runReturnUses = bufferConfig.outputs.map(([name, _]) => `res_${name}`).join(" ");
	return [
		"import Risc0.Lemmas",
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"",
		"def full : MLIRProgram :=",
		IR.irLinesToLean(witnessFullLines),
		getWitnessReturn(witness, bufferConfig),
		`def run (st: State) ${runReturnParams}: Prop :=`,
		`  getReturn (full.runProgram st) ${runReturnUses}`,
		"",
		"end Code",
		"",
		// TODO generalize start state
		`def start_state ${startStateInputs} : State :=`,
		`  { buffers := Map.fromList [${startStateBuffers}]`,
		`  , felts := Map.empty`,
		`  , props := Map.empty`,
		`  , isFailed := false`,
		`  , bufferWidths := Map.fromList [${startStateBufferWidths}]`,
		`  , cycle := 0`,
		`  , vars := [${startStateBufferVars}]`,
		`  }`,
		"",
		`end Risc0.${funcName}.Witness`,
		""
	].join("\n");
}

function createConstraintsCodeLean(funcName: string, constraints: string[], argIdToName: Map<string, string>, linesPerPart: number, bufferConfig: BufferConfig): string {
	const constraintsFullLines = parseBody(constraints, argIdToName);
	const startStateInputs = `(${[
		...bufferConfig.inputs.map(([name, _]) => `input_${name}`),
		...bufferConfig.outputs.map(([name, _]) => `output_${name}`),
	].join(" ")}: BufferAtTime)`;
	const startStateBuffers = [
		...bufferConfig.inputs.map(([name, _]) => `(⟨"${name}"⟩, [input_${name}])`),
		...bufferConfig.outputs.map(([name, width]) => `(⟨"${name}"⟩, [output_${name}])`)
	].join(", ");
	const startStateBufferWidths = [
		...bufferConfig.inputs.map(([name, width]) => `(⟨"${name}"⟩, ${width})`),
		...bufferConfig.outputs.map(([name, width]) => `(⟨"${name}"⟩, ${width})`)
	].join(", ");
	const startStateBufferVars = [
		...bufferConfig.inputs.map(([name, _]) => `⟨"${name}"⟩`),
		...bufferConfig.outputs.map(([name, _]) => `⟨"${name}"⟩`)
	].join(", ");
	return [
		"import Risc0.Lemmas",
		"",
		`namespace Risc0.${funcName}.Constraints.Code`,
		"",
		"open MLIRNotation",
		"",
		"def full : MLIRProgram :=",
		IR.irLinesToLean(constraintsFullLines),
		getConstraintsReturn(constraints),
		"def run (st: State) : Prop :=",
		"  getReturn (full.runProgram st)",
		"",
		"end Code",
		"",
		// TODO generalize start state
		`def start_state ${startStateInputs} : State :=`,
		`  { buffers := Map.fromList [${startStateBuffers}]`,
		`  , felts := Map.empty`,
		`  , props := Map.empty`,
		`  , isFailed := false`,
		`  , bufferWidths := Map.fromList [${startStateBufferWidths}]`,
		`  , cycle := 0`,
		`  , vars := [${startStateBufferVars}]`,
		`  }`,
		"",
		`end Risc0.${funcName}.Constraints`,
		""
	].join("\n");
}

function createConstraintsCodeReorderedLean(funcName: string, witness: string[], argIdToName: Map<string, string>): [ir: IR.Statement[], lean: string] {
	const IR = parseBody(witness, argIdToName);
	const [reorderedIR, reorderedLean] = getStepwiseOptimisations(IR, []);
	console.log(`Reordered constraints code:`);
	reorderedIR.forEach(x => console.log(x.toString()));
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
			`end Risc0.${funcName}.Constraints.Code`,
		].join("\n")
	];
}

function createWitnessCodeReorderedLean(funcName: string, witness: string[], argIdToName: Map<string, string>): [ir: IR.Statement[], lean: string] {
	const IR = parseBody(witness, argIdToName);
	const [reorderedIR, reorderedLean] = getStepwiseOptimisations(IR, ["res"]); // TODO generalise
	console.log(`Reordered witness code:`);
	reorderedIR.forEach(x => console.log(x.toString()));
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
			`end Risc0.${funcName}.Witness.Code`,
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

function excludeFiles(prefix: string, funcName: string): string[] {
	return commentInImportFile(prefix, (x) => x.includes(`.${funcName}.`));
}
