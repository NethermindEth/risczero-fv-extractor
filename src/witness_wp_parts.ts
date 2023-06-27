import { exec } from 'child_process';
import fs from 'fs';
import { addToImportFile } from './util';

const skipFirst = false;
const skipMid = false;
const skipToMid: number | null = null; // set to null to turn off

export function witnessWeakestPreFiles(leanPath: string, funcName: string, parts: number, bufferWidth: number) {
	console.log("Creating witness weakest pre files");
	if (skipFirst) {
		if (skipToMid === null) {
			recurseThroughMidFiles(leanPath, funcName, 1, parts, bufferWidth);
		} else {
			recurseThroughMidFiles(leanPath, funcName, skipToMid, parts, bufferWidth);
		}
	} else {
		const part0 = witnessWeakestPrePart0(funcName, parts, bufferWidth, "sorry");
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart0.lean`, part0);
		addToImportFile(leanPath, `${funcName}.Witness.WeakestPresPart0`)
		console.log("  0 - sorry");
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const stateTransformer = extractStateTransformer(stderr, funcName, 0);
			console.log(stateTransformer);
			const part0 = witnessWeakestPrePart0(funcName, parts, bufferWidth, stateTransformer);
			console.log("  0 - corrected");
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart0.lean`, part0);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				if (skipToMid === null) {
					recurseThroughMidFiles(leanPath, funcName, 1, parts, bufferWidth);
				} else {
					recurseThroughMidFiles(leanPath, funcName, skipToMid, parts, bufferWidth);
				}
			});
		});
	}
}

function recurseThroughMidFiles(leanPath: string, funcName: string, part: number, parts: number, bufferWidth: number) {
	if (skipMid) {
		lastFile(leanPath, funcName, parts, bufferWidth);
	} else {
		const mid = witnessWeakestPreMid(funcName, part, parts, bufferWidth, "sorry");
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart${part}.lean`, mid);
		addToImportFile(leanPath, `${funcName}.Witness.WeakestPresPart${part}`)
		console.log(`  ${part} - sorry`);
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const stateTransformer = extractStateTransformer(stderr, funcName, part);
			console.log(stateTransformer);
			const mid = witnessWeakestPreMid(funcName, part, parts, bufferWidth, stateTransformer);
			console.log(`  ${part} - corrected`);
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart${part}.lean`, mid);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				const fixed = fixInvalidNotation(stderr, mid);
				if (fixed !== null) {
					fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart${part}.lean`, fixed);
				}
				if (part+1 < parts) {
					recurseThroughMidFiles(leanPath, funcName, part+1, parts, bufferWidth);
				} else {
					lastFile(leanPath, funcName, parts, bufferWidth);
				}
			});
		});
	}
}

function lastFile(leanPath: string, funcName: string, parts: number, bufferWidth: number) {
	const part = parts-1;
	const last = witnessWeakestPreLast(funcName, parts, bufferWidth, "sorry");
	fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart${part}.lean`, last);
	addToImportFile(leanPath, `${funcName}.Witness.WeakestPresPart${part}`)
	console.log(`  ${part} - sorry`);
	exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
		const stateTransformer = extractStateTransformerLast(stderr, funcName, part);
		console.log(stateTransformer);
		const last = witnessWeakestPreLast(funcName, parts, bufferWidth, stateTransformer);
		console.log(`  ${part} - corrected`);
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Witness/WeakestPresPart${part}.lean`, last);
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
			}
			console.log("Done")
		});
	});
}

function witnessWeakestPrePart0(funcName: string, parts: number, bufferWidth: number, stateTransformer: string): string {
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Witness.Code`,
		``,
		`namespace Risc0.${funcName}.Witness.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part0 on st`,
		`def part0_state (st: State) : State :=`,
		`  ${stateTransformer}`,
		``,
		`-- Run the whole program by using part0_state rather than Code.part0`,
		`def part0_state_update (st: State): State :=`,
		`  Γ (part0_state st) ⟦${codePartsRange(1, parts)}⟧`,
		``,
		`-- Prove that substituting part0_state for Code.part0 produces the same result`,
		`lemma part0_wp {st : State} {${variableList("y", " ", bufferWidth)} : Option Felt} :`,
		`  Code.run st = [${variableList("y", ", ", bufferWidth)}] ↔`,
		`  Code.getReturn (part0_state_update st) = [${variableList("y", ", ", bufferWidth)}] := by`,
		`  unfold Code.run MLIR.runProgram; simp only`,
		`  rewrite [←Code.parts_combine]; unfold Code.parts_combined`,
		`  generalize eq : (${codePartsRange(1, parts)}) = prog`,
		`  unfold Code.part0`,
		`  MLIR`,
		`  unfold part0_state_update part0_state`,
		`  rewrite [←eq]`,
		`  rfl`,
		``,
		`end Risc0.${funcName}.Witness.WP`,
	].join("\n");
}

function witnessWeakestPreMid(funcName: string, part: number, parts: number, bufferWidth: number, stateTransformer: string): string {
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Witness.Code`,
		`import Risc0.Gadgets.${funcName}.Witness.WeakestPresPart${part-1}`,
		``,
		`namespace Risc0.${funcName}.Witness.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part${part} on st`,
		`def part${part}_state (st: State) : State :=`,
		`  ${stateTransformer}`,
		``,
		`-- Run the program from part${part} onwards by using part${part}_state rather than Code.part${part}`,
		`def part${part}_state_update (st: State): State :=`,
		`  Γ (part${part}_state st) ⟦${codePartsRange(part+1, parts)}⟧`,
		``,
		`-- Prove that substituting part${part}_state for Code.part${part} produces the same result`,
		`lemma part${part}_wp {st : State} {${variableList("y", " ", bufferWidth)} : Option Felt} :`,
		`  Code.getReturn (MLIR.runProgram (${codePartsRange(part, parts)}) st) = [${variableList("y", ", ", bufferWidth)}] ↔`,
		`  Code.getReturn (part${part}_state_update st) = [${variableList("y", ", ", bufferWidth)}] := by`,
		`  unfold MLIR.runProgram; simp only`,
		`  generalize eq : (${codePartsRange(part+1, parts)}) = prog`,
		`  unfold Code.part${part}`,
		`  MLIR`,
		`  rewrite [←eq]`,
		`  unfold part${part}_state_update part${part}_state`,
		`  rfl`,
		``,
		`lemma part${part}_updates_opaque {st : State} : `,
		`  Code.getReturn (part${part-1}_state_update st) = [${variableList("y", ", ", bufferWidth)}] ↔`,
		`  Code.getReturn (part${part}_state_update (part${part-1}_state st)) = [${variableList("y", ", ", bufferWidth)}] := by`,
		`  simp [part${part-1}_state_update, part${part}_wp]`,
		``,
		`end Risc0.${funcName}.Witness.WP`,
	].join("\n");
}

function witnessWeakestPreLast(funcName: string, parts: number, bufferWidth: number, stateTransformer: string): string {
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Witness.Code`,
		`import Risc0.Gadgets.${funcName}.Witness.WeakestPresPart${parts-2}`,
		``,
		`namespace Risc0.${funcName}.Witness.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part${parts-1} on st`,
		`def part${parts-1}_state (st: State) : State := `,
		`  ${stateTransformer}`,
		``,
		`-- Prove that substituting part${parts-1}_state for Code.part${parts-1} produces the same result`,
		`lemma part${parts-1}_wp {st : State} {${variableList("y", " ", bufferWidth)} : Option Felt} :`,
		`  Code.getReturn (MLIR.runProgram Code.part${parts-1} st) = [${variableList("y", ", ", bufferWidth)}] ↔`,
		`  Code.getReturn (part${parts-1}_state st) = [${variableList("y", ", ", bufferWidth)}] := by`,
		`  unfold MLIR.runProgram; simp only`,
		`  unfold Code.part${parts-1}`,
		`  MLIR`,
		`  unfold part${parts-1}_state`,
		`  rfl`,
		``,
		`lemma part${parts-1}_updates_opaque {st : State} : `,
		`  Code.getReturn (part${parts-2}_state_update st) = [${variableList("y", ", ", bufferWidth)}] ↔`,
		`  Code.getReturn (part${parts-1}_state (part${parts-2}_state st)) = [${variableList("y", ", ", bufferWidth)}] := by`,
		`  simp [part${parts-2}_state_update, part${parts-1}_wp]`,
		``,
		`end Risc0.${funcName}.Witness.WP`,
	].join("\n");
}

function codePartsRange(start: number, end: number): string {
	let result = `Code.part${start}`;
	for (let i = start + 1; i < end; ++i) {
		result = `${result}; Code.part${i}`;
	}
	return result;
}

function extractStateTransformer(stderr: string, funcName: string, part: number): string {
	const searchStart = stderr.indexOf(`${funcName}/Witness/WeakestPresPart${part}.lean:`);
	const gammaIdx = stderr.indexOf("Γ", searchStart);
	const codeStart = stderr.indexOf("⟦", gammaIdx);
	return stderr.slice(gammaIdx+1, codeStart);
}

function extractStateTransformerLast(stderr: string, funcName: string, part: number): string {
	const searchStart = stderr.indexOf(`${funcName}/Witness/WeakestPresPart${part}.lean:`);
	const startIdx = stderr.indexOf("Code.getReturn", searchStart) + "Code.getReturn".length;
	const iffIdx = stderr.indexOf("↔", startIdx);
	const endIdx = stderr.slice(0, iffIdx).lastIndexOf("=");
	return stderr.slice(startIdx, endIdx);
}

function variableList(name: string, separator: string, count: number): string {
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