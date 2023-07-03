import { exec } from 'child_process';
import fs from 'fs';
import { addToImportFile } from './util';
import { IR } from './IR';

const skipFirst = false;
const skipMid = false;
const skipToMid: number | null = null; // set to null to turn off

export function constraintsWeakestPreFiles(leanPath: string, funcName: string, ir: IR.Statement[], linesPerPart: number, partDrops: IR.DropFelt[][], bufferWidth: number, callback: ()=>void) {
	console.log("Creating constraints weakest pre files");
	if (skipFirst) {
		if (skipToMid === null) {
			recurseThroughMidFiles(leanPath, funcName, 1, ir , linesPerPart, partDrops, bufferWidth, callback);
		} else {
			recurseThroughMidFiles(leanPath, funcName, skipToMid, ir, linesPerPart, partDrops, bufferWidth, callback);
		}
	} else {
		const part0 = constraintsWeakestPrePart0(funcName, partDrops, bufferWidth, undefined, undefined);
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart0.lean`, part0);
		addToImportFile(leanPath, `${funcName}.Constraints.WeakestPresPart0`)
		console.log("  0 - sorry");
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const [stateTransformer, cumulativeTransformer] = extractStateTransformers(stderr, funcName, 0);
			console.log(`State transformer: "${stateTransformer}"`);
			console.log(`Cumulative transformer: "${cumulativeTransformer}"`);
			const part0 = constraintsWeakestPrePart0(funcName, partDrops, bufferWidth, stateTransformer, cumulativeTransformer);
			console.log("  0 - corrected");
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart0.lean`, part0);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				if (skipToMid === null) {
					recurseThroughMidFiles(leanPath, funcName, 1, ir , linesPerPart, partDrops, bufferWidth, callback);
				} else {
					recurseThroughMidFiles(leanPath, funcName, skipToMid, ir, linesPerPart, partDrops, bufferWidth, callback);
				}
			});
		}).stdout?.pipe(process.stdout);
	}
}

function recurseThroughMidFiles(leanPath: string, funcName: string, part: number, ir: IR.Statement[], linesPerPart: number, partDrops: IR.DropFelt[][], bufferWidth: number, callback: ()=>void) {
	if (skipMid) {
		lastFile(leanPath, funcName, ir, linesPerPart, partDrops, bufferWidth, callback);
	} else {
		console.log(`Part ${part} of ${partDrops.length}`);
		const mid = constraintsWeakestPreMid(funcName, part, ir, linesPerPart, partDrops, bufferWidth, undefined, undefined);
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, mid);
		addToImportFile(leanPath, `${funcName}.Constraints.WeakestPresPart${part}`)
		console.log(`  ${part} - sorry`);
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const [stateTransformer, cumulativeTransformer] = extractStateTransformers(stderr, funcName, part);
			console.log(`State transformer: "${stateTransformer}"`);
			console.log(`Cumulative transformer: "${cumulativeTransformer}"`);
			const mid = constraintsWeakestPreMid(funcName, part, ir, linesPerPart, partDrops, bufferWidth, stateTransformer, cumulativeTransformer);
			console.log(`  ${part} - corrected`);
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, mid);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				const fixed = fixInvalidNotation(stderr, mid);
				if (fixed !== null) {
					fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, fixed);
				}
				if (part+1 < partDrops.length - 1) {
					recurseThroughMidFiles(leanPath, funcName, part+1, ir, linesPerPart, partDrops, bufferWidth, callback);
				} else {
					lastFile(leanPath, funcName, ir, linesPerPart, partDrops, bufferWidth, callback);
				}
			}).stdout?.pipe(process.stdout);
		}).stdout?.pipe(process.stdout);
	}
}

function lastFile(leanPath: string, funcName: string, ir: IR.Statement[], linesPerPart: number, partDrops: IR.DropFelt[][], bufferWidth: number, callback: ()=>void) {
	const part = partDrops.length-1;
	const last = constraintsWeakestPreLast(funcName, ir, linesPerPart, partDrops, bufferWidth, undefined, undefined, undefined);
	fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, last);
	addToImportFile(leanPath, `${funcName}.Constraints.WeakestPresPart${part}`)
	console.log(`  ${part} - sorry`);
	exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
		const [stateTransformer, cumulativeTransformer] = extractStateTransformers(stderr, funcName, part);
		console.log(`State transformer: "${stateTransformer}"`);
		console.log(`Cumulative transformer: "${cumulativeTransformer}"`);
		const last = constraintsWeakestPreLast(funcName, ir, linesPerPart, partDrops, bufferWidth, stateTransformer, cumulativeTransformer, undefined);
		console.log(`  ${part} - corrected`);
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, last);
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const closedForm = extractClosedForm(stderr);
			console.log(closedForm);
			const last = constraintsWeakestPreLast(funcName, ir, linesPerPart, partDrops, bufferWidth, stateTransformer, cumulativeTransformer, closedForm);
			console.log(`  closed form`);
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, last);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				callback();
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
				}
				console.log("Done")
			}).stdout?.pipe(process.stdout);
		}).stdout?.pipe(process.stdout);
	}).stdout?.pipe(process.stdout);
}

function constraintsWeakestPrePart0(funcName: string, partDrops: IR.DropFelt[][], bufferWidth: number, stateTransformer: string | undefined, cumulativeTransformer: string | undefined): string {
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Constraints.CodeDrops`,
		``,
		`namespace Risc0.${funcName}.Constraints.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part0 on st`,
		`def part0_state (st: State) : State :=`,
		`  ${stateTransformer ?? "sorry"}`,
		``,
		`def part0_drops (st: State) : State :=`,
		`  ${getPartDropsDef(partDrops[0])}`,
		``,
		`-- Run the whole program by using part0_state rather than Code.part0`,
		`def part0_state_update (st: State): State :=`,
		`  Γ (part0_drops (part0_state st)) ⟦${codePartsRange(1, partDrops, true)}⟧`,
		``,
		`-- Prove that substituting part0_state for Code.part0 produces the same result`,
		`lemma part0_wp {st : State} :`,
		`  Code.getReturn (Γ st ⟦${codePartsRange(0, partDrops, true)}⟧)↔`,
		`  Code.getReturn (part0_state_update st) := by`,
		`  generalize eq : (${codePartsRange(0, partDrops, false)}) = prog`,
		`  unfold Code.part0`,
		`  MLIR`,
		...(stateTransformer === undefined
			? []
			: [
				`  rewrite [←eq]`,
				`  ${getDropEvaluationRewrites(partDrops, 0)}`,
				`  unfold part0_state_update part0_drops part0_state`,
				`  rfl`,
			]
		),
		``,
		`lemma part0_cumulative_wp {${variableList("x"," ",4)} ${variableList("y"," ",bufferWidth)}: Felt}:`,
		`  Code.run (start_state [${variableList("x",",",4)}] ([${variableList("y",",",bufferWidth)}])) ↔`,
		`  ${cumulativeTransformer ?? "sorry"} := by`,
		`    unfold Code.run start_state`,
		`    rewrite [Code.optimised_behaviour_full]`,
		`    unfold MLIR.runProgram`,
		`    rewrite [←Code.parts_combine]`,
		`    unfold Code.parts_combined`,
		`    rewrite [←Code.getReturn_ignores_drops]`,
		`    rewrite [←Code.behaviour_with_drops]`,
		`    rewrite [part0_wp]`,
		`    rfl`,
		``,
		`end Risc0.${funcName}.Constraints.WP`,
	].join("\n");
}

function constraintsWeakestPreMid(
	funcName: string,
	part: number,
	ir: IR.Statement[],
	linesPerPart: number,
	partDrops: IR.DropFelt[][],
	bufferWidth: number,
	stateTransformer: string | undefined,
	cumulativeTransformer: string | undefined
): string {
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Constraints.Code`,
		`import Risc0.Gadgets.${funcName}.Constraints.WeakestPresPart${part-1}`,
		``,
		`namespace Risc0.${funcName}.Constraints.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part${part} on st`,
		`def part${part}_state (st: State) : State :=`,
		`  ${stateTransformer ?? "sorry"}`,
		``,
		`def part${part}_drops (st: State) : State :=`,
		`  ${getPartDropsDef(partDrops[part])}`,
		``,
		`-- Run the program from part${part} onwards by using part${part}_state rather than Code.part${part}`,
		`def part${part}_state_update (st: State): State :=`,
		`  Γ (part${part}_drops (part${part}_state st)) ⟦${codePartsRange(part+1, partDrops, true)}⟧`,
		``,
		`-- Prove that substituting part${part}_state for Code.part${part} produces the same result`,
		`lemma part${part}_wp {st : State} :`,
		`  Code.getReturn (MLIR.runProgram (${codePartsRange(part, partDrops, true)}) st) ↔`,
		`  Code.getReturn (part${part}_state_update st) := by`,
		`  unfold MLIR.runProgram; simp only`,
		`  generalize eq : (${codePartsRange(part, partDrops, false)}) = prog`,
		`  unfold Code.part${part}`,
		`  MLIR`,
		...(stateTransformer === undefined
			? []
			: [
				`  rewrite [←eq]`,
				`  ${getDropEvaluationRewrites(partDrops, part)}`,
				`  unfold part${part}_state_update part${part}_drops part${part}_state`,
				`  rfl`,
			]
		),
		``,
		`lemma part${part}_updates_opaque {st : State} : `,
		`  Code.getReturn (part${part-1}_state_update st) ↔`,
		`  Code.getReturn (part${part}_state_update (part${part-1}_drops (part${part-1}_state st))) := by`,
		`  simp [part${part-1}_state_update, part${part}_wp]`,
		``,
		// TODO extract input width constant
		`lemma part${part}_cumulative_wp {${variableList("x"," ",4)} ${variableList("y"," ",bufferWidth)}: Felt} :`,
		`  Code.run (start_state [${variableList("x",",",4)}] ([${variableList("y",",",bufferWidth)}])) ↔`,
		`  ${cumulativeTransformer ?? "sorry"} := by`,
		cumulative_wp_proof(part, ir, linesPerPart, partDrops, cumulativeTransformer === undefined),
		``,
		`end Risc0.${funcName}.Constraints.WP`,
	].join("\n");
}

function cumulative_wp_proof(part: number, ir: IR.Statement[], linesPerPart: number, partDrops: IR.DropFelt[][], firstPass: boolean): string {
	const dropCount = partDrops[part-1].length;
	const previousPart = ir.slice((part-1)*linesPerPart, part*linesPerPart);
	const setCount = previousPart.filter(stmt => stmt.kind === "set").length;
	const eqzCount = previousPart.filter(stmt => stmt.kind === "eqz").length;
	return [
		`    rewrite [part${part-1}_cumulative_wp]`,
		part === partDrops.length
			? `    unfold part${part-1}_state_update`
			: `    rewrite [part${part}_updates_opaque]`,
		`    unfold part${part-1}_state`,
		`    MLIR_states_updates`,
		`    -- ${eqzCount} withEqZero${eqzCount === 1 ? "" : "s"}`,
		Array(Math.max(1,eqzCount)).fill([
			`    ${eqzCount === 0 ? "-- " : ""}rewrite [withEqZero_def]`,
			`    ${eqzCount === 0 ? "-- " : ""}MLIR_states_updates`,
		].join("\n")).join("\n"),
		`    unfold part${part-1}_drops`,
		`    -- ${dropCount} drop${dropCount === 1 ? "" : "s"}`,
		`    ${dropCount === 0 ? "-- " : ""}simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]`,
		`    ${dropCount === 0 ? "-- " : ""}rewrite [State.dropFelts]`,
		`    ${dropCount === 0 ? "-- " : ""}simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]`,
		`    ${dropCount === 0 ? "-- " : ""}simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]`,
		`    -- ${setCount} set${setCount === 1 ? "" : "s"}`,
		`    ${setCount === 0 ? "-- " : ""}rewrite [Map.drop_of_updates]`,
		`    ${setCount === 0 ? "-- " : ""}simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]`,
		...(firstPass || (dropCount + setCount + eqzCount === 0) ? [`    rfl`] : []),
	].join("\n");
}

function constraintsWeakestPreLast(
	funcName: string,
	ir: IR.Statement[],
	linesPerPart: number,
	partDrops: IR.DropFelt[][],
	bufferWidth: number,
	stateTransformer: string | undefined,
	cumulativeTransformer: string | undefined,
	closedForm: string | undefined,
): string {
	const part = partDrops.length-1;
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Constraints.Code`,
		`import Risc0.Gadgets.${funcName}.Constraints.WeakestPresPart${part-1}`,
		``,
		`namespace Risc0.${funcName}.Constraints.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part${part} on st`,
		`def part${part}_state (st: State) : State :=`,
		`  ${stateTransformer ?? "sorry"}`,
		``,
		`def part${part}_drops (st: State) : State :=`,
		`  ${getPartDropsDef(partDrops[part])}`,
		``,
		`-- Run the program from part${part} onwards by using part${part}_state rather than Code.part${part}`,
		`def part${part}_state_update (st: State): State :=`,
		`  part${part}_drops (part${part}_state st)`,
		``,
		`-- Prove that substituting part${part}_state for Code.part${part} produces the same result`,
		`lemma part${part}_wp {st : State}:`,
		`  Code.getReturn (MLIR.runProgram (${codePartsRange(part, partDrops, true)}) st) ↔`,
		`  Code.getReturn (part${part}_state_update st) := by`,
		`  unfold MLIR.runProgram; simp only`,
		`  generalize eq : (${codePartsRange(part, partDrops, false)}) = prog`,
		`  unfold Code.part${part}`,
		`  MLIR`,
		...(stateTransformer === undefined
			? []
			: [
				`  rewrite [←eq]`,
				`  ${getDropEvaluationRewrites(partDrops, part)}`,
				`  unfold part${part}_state_update part${part}_drops part${part}_state`,
				`  rfl`,
			]
		),
		``,
		`lemma part${part}_updates_opaque {st : State} : `,
		`  Code.getReturn (part${part-1}_state_update st) ↔`,
		`  Code.getReturn (part${part}_state_update (part${part-1}_drops (part${part-1}_state st))) := by`,
		`  simp [part${part-1}_state_update, part${part}_wp]`,
		``,
		// TODO extract input width constant
		`lemma part${part}_cumulative_wp {${variableList("x"," ",4)} ${variableList("y"," ",18)}: Felt} :`,
		`  Code.run (start_state [${variableList("x",",",4)}] ([${variableList("y",",",bufferWidth)}])) ↔`,
		`  ${cumulativeTransformer ?? "sorry"} := by`,
		cumulative_wp_proof(part, ir, linesPerPart, partDrops, cumulativeTransformer === undefined),
		``,
		...(cumulativeTransformer === undefined
			? []
			: [
				`lemma closed_form {${variableList("x"," ",4)} ${variableList("y"," ",bufferWidth)}: Felt} :`,
				`  Code.run (start_state [${variableList("x",",",4)}] ([${variableList("y",",",bufferWidth)}])) ↔`,
				`  ${closedForm ?? "sorry"} := by`,
				cumulative_wp_proof(part+1, ir, linesPerPart, partDrops, false),
				`    unfold Code.getReturn`,
				`    simp only`,
				`    simp only [Code.getReturn, State.constraintsInVar, State.updateProps_props_get_wobbly, Option.getD_some]`,
			]
		),
		`end Risc0.${funcName}.Constraints.WP`,
	].join("\n");
}

function getPartDropsDef(drops: IR.DropFelt[]): string {
	return drops.reduce((st, drop) => `State.dropFelts (${st}) ⟨"${drop.val}"⟩`, "st");
}

function getDropEvaluationRewrites(drops: IR.DropFelt[][], part: number): string {
	if (drops[part].length === 0) {
		return "";
	} else {
		return `rewrite [${drops[part].map((_,idx) => 
			part === drops.length - 1 && idx === drops[part].length - 1
				? "MLIR.run_dropfelt"
				: "MLIR.run_seq_def,MLIR.run_dropfelt"
		).join(", ")}]`;
	}
}

// includeFirstPart is the different between part${start};drops;part${start+1}... and drops;part${start+1}
export function codePartsRange(start: number, drops: IR.DropFelt[][], includeFirstPart: boolean): string {
	return drops
		.slice(start)
		.flatMap((drops, index) => [
			...(index===0 && !includeFirstPart ? [] : [`Code.part${index+start}`]),
			...drops.map(d => d.toString())
		]).join(";");
}

function extractStateTransformers(stderr: string, funcName: string, part: number): [stateTransformer: string, cumulativeTransformer: string] {
	// console.log(`STDERR----------------\n${stderr.split("\n").join("----\n----")}\n-------------`);
	const firstErrorStart = stderr.split("\n").findIndex(line => line.includes(`${funcName}/Constraints/WeakestPresPart${part}.lean:`) && line.includes("error: unsolved goals"));
	// console.log(`First error start line: ${firstErrorStart}`);
	const secondErrorStart = stderr.split("\n").slice(firstErrorStart+1).findIndex(line => line.includes(`${funcName}/Constraints/WeakestPresPart${part}.lean:`) && line.includes("error: type mismatch")) + firstErrorStart + 1;
	// console.log(`Second error start line: ${secondErrorStart}`);
	const firstError = stderr.split("\n").slice(firstErrorStart, secondErrorStart).join("\n");
	const secondError = stderr.split("\n").slice(secondErrorStart).join("\n");
	// console.log(`FIRST ERROR--\n--\n--\n${firstError}`);
	// console.log(`\n\n\n\nSECOND ERROR--\n--\n--\n${secondError}`);

	const gammaIdx = firstError.indexOf("Γ");
	const codeStart = firstError.indexOf("⟦", gammaIdx);
	const stateTransformer = firstError.slice(gammaIdx+1, codeStart);

	const getReturnIdx = secondError.indexOf("Code.getReturn");
	const iffIdx = secondError.indexOf("↔");
	const cumulativeTransformer = secondError.slice(getReturnIdx, iffIdx);

	if (stateTransformer.trim() === "") {
		throw "Failed to extract state transformer from lake error message. There is likely an unexpected error";
	}
	if (cumulativeTransformer.trim() === "") {
		throw "Failed to extract cumulative transformer from lake error message. There is likely an unexpected error";
	}
	return [stateTransformer, cumulativeTransformer];
}

function extractClosedForm(stderr: string): string {
	const startIdx = stderr.indexOf("⊢") + 1;
	const endIdx = stderr.indexOf("↔")
	return stderr.slice(startIdx, endIdx);
}

export function variableList(name: string, separator: string, count: number): string {
	let result = `${name}0`;
	for (let i = 1; i < count; ++i) {
		result = `${result}${separator}${name}${i}`;
	}
	return result;
}

function fixInvalidNotation(stderr: string, code: string): string | null {
	const res = invalidNotationCheck(stderr);
	if (res.length === 0) {
		return null;
	}

	for (let i = 0; i < res.length; ++i) {
		const [line, column] = res[i];
		const codeLines = code.split("\n");
		const codeLine = codeLines[line-1]; // line-1 because the line number is 1-indexed
		const endIdx = codeLine.indexOf("}]!", column) + 1;
		codeLines[line-1] = `${codeLine.slice(0, column)}(${codeLine.slice(column, endIdx)}: FeltVar)${codeLine.slice(endIdx)}`;
		code = codeLines.join("\n");
	}
	console.log("Notation fixed");
	return code;
}

function invalidNotationCheck(stderr: string): [line: number, col: number][] {
	const idx = stderr.lastIndexOf("invalid {...} notation");
	if (idx === -1) {
		return [];
	}
	const slice = stderr.slice(0, idx);
	const lineNumStart = slice.lastIndexOf(".lean:") + ".lean:".length;
	const lineNumEnd = slice.indexOf(":", lineNumStart);
	const columnNumStart = lineNumEnd+1;
	const columnNumEnd = slice.indexOf(":", columnNumStart);
	return [
		[parseInt(slice.slice(lineNumStart, lineNumEnd)), parseInt(slice.slice(columnNumStart, columnNumEnd))],
		...invalidNotationCheck(stderr.slice(0, idx))
	];
}