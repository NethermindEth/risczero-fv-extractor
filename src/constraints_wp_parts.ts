import { exec } from 'child_process';
import fs from 'fs';
import { addToImportFile } from './util';

const skipFirst = false;
const skipMid = false;

export function constraintsWeakestPreFiles(leanPath: string, funcName: string, parts: number, callback: () => void) {
	console.log("Creating constraints weakest pre files");
	if (skipFirst) {
		recurseThroughMidFiles(leanPath, funcName, 1, parts, callback);
	} else {
		const part0 = constraintsWeakestPrePart0(funcName, parts, "sorry");
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart0.lean`, part0);
		addToImportFile(leanPath, `${funcName}.Constraints.WeakestPresPart0`)
		console.log("  0 - sorry");
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const stateTransformer = extractStateTransformer(stderr, funcName, 0);
			console.log(stateTransformer);
			const part0 = constraintsWeakestPrePart0(funcName, parts, stateTransformer);
			console.log("  0 - corrected");
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart0.lean`, part0);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				recurseThroughMidFiles(leanPath, funcName, 1, parts, callback);
			});
		});
	}
}

function recurseThroughMidFiles(leanPath: string, funcName: string, part: number, parts: number, callback: () => void) {
	if (skipMid) {
		lastFile(leanPath, funcName, parts, callback);
	} else {
		const mid = constraintsWeakestPreMid(funcName, part, parts, "sorry");
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, mid);
		addToImportFile(leanPath, `${funcName}.Constraints.WeakestPresPart${part}`)
		console.log(`  ${part} - sorry`);
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			const stateTransformer = extractStateTransformer(stderr, funcName, part);
			console.log(stateTransformer);
			const mid = constraintsWeakestPreMid(funcName, part, parts, stateTransformer);
			console.log(`  ${part} - corrected`);
			fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, mid);
			exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
				if (part+1 < parts) {
					recurseThroughMidFiles(leanPath, funcName, part+1, parts, callback);
				} else {
					lastFile(leanPath, funcName, parts, callback);
				}
			});
		});
	}
}

function lastFile(leanPath: string, funcName: string, parts: number, callback: () => void) {
	const part = parts-1;
	const last = constraintsWeakestPreLast(funcName, parts, "sorry");
	fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, last);
	addToImportFile(leanPath, `${funcName}.Constraints.WeakestPresPart${part}`)
	console.log(`  ${part} - sorry`);
	exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
		const stateTransformer = extractStateTransformerLast(stderr, funcName, part);
		console.log(stateTransformer);
		const last = constraintsWeakestPreLast(funcName, parts, stateTransformer);
		console.log(`  ${part} - corrected`);
		fs.writeFileSync(`${leanPath}/Risc0/Gadgets/${funcName}/Constraints/WeakestPresPart${part}.lean`, last);
		exec(`cd ${leanPath}; lake build`, (error, stdout, stderr) => {
			callback();
		});
	});
}

function constraintsWeakestPrePart0(funcName: string, parts: number, stateTransformer: string): string {
	return [
		"import Risc0.Basic",
		"import Risc0.MlirTactics",
		`import Risc0.Gadgets.${funcName}.Constraints.Code`,
		"",
		`namespace Risc0.${funcName}.Constraints.WP`,
		"",
		"open MLIRNotation",
		"",
		"-- The state obtained by running Code.part0 on st",
		"def part0_state (st : State) : State :=",
		`  ${stateTransformer}`,
		"",
		"-- Run the whole program by using part0_state rather than Code.part0",
		"def part0_state_update (st : State) : State :=",
		`  Γ (part0_state st) ⟦${codePartsRange(1, parts)}⟧`,
		"",
		"-- Prove that substituting part0_state for Code.part0 produces the same result",
		"lemma part0_wp {st : State} :",
		"  Code.run st ↔",
		"  Code.getReturn (part0_state_update st) := by",
		"    unfold Code.run MLIR.runProgram; simp only",
		"    rewrite [←Code.parts_combine]; unfold Code.parts_combined",
		`    generalize eq : (${codePartsRange(1, parts)}) = prog`,
		"    unfold Code.part0",
		"    MLIR",
		"    unfold part0_state_update part0_state",
		"    rw [←eq]",
		"",
		`end Risc0.${funcName}.Constraints.WP`,
	].join("\n");
}

function constraintsWeakestPreMid(funcName: string, part: number, parts: number, stateTransformer: string): string {
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
		`def part${part}_state (st: State) : State := `,
		`  ${stateTransformer}`,
		``,
		`-- Run the whole program by using part${part}_state rather than Code.part${part}`,
		`def part${part}_state_update (st: State): State :=`,
		`  Γ (part${part}_state st) ⟦${codePartsRange(part+1, parts)}⟧`,
		``,
		`-- Prove that substituting part${part}_state for Code.part${part} produces the same result`,
		`lemma part${part}_wp {st : State} :`,
		`  Code.getReturn (MLIR.runProgram (${codePartsRange(part, parts)}) st) ↔`,
		`  Code.getReturn (part${part}_state_update st) := by`,
		`  unfold MLIR.runProgram; simp only`,
		`  generalize eq : (${codePartsRange(part+1, parts)}) = prog`,
		`  unfold Code.part${part}`,
		`  MLIR`,
		`  unfold part${part}_state_update part${part}_state`,
		`  rewrite [←eq]`,
		`  rfl`,
		``,
		`lemma part${part}_updates_opaque {st : State} : `,
		`  Code.getReturn (part${part-1}_state_update st) ↔`,
		`  Code.getReturn (part${part}_state_update (part${part-1}_state st)) := by`,
		`  simp [part${part-1}_state_update, part${part}_wp]`,
		``,
		`end Risc0.${funcName}.Constraints.WP`,
	].join("\n");
}

function constraintsWeakestPreLast(funcName: string, parts: number, stateTransformer: string): string {
	return [
		`import Risc0.Basic`,
		`import Risc0.MlirTactics`,
		`import Risc0.Gadgets.${funcName}.Constraints.Code`,
		`import Risc0.Gadgets.${funcName}.Constraints.WeakestPresPart${parts-2}`,
		``,
		`namespace Risc0.${funcName}.Constraints.WP`,
		``,
		`open MLIRNotation`,
		``,
		`-- The state obtained by running Code.part${parts-1} on st`,
		`def part${parts-1}_state (st: State) : State := `,
		`  ${stateTransformer}`,
		``,
		`-- Prove that substituting part${parts-1}_state for Code.part${parts-1} produces the same result`,
		`lemma part${parts-1}_wp {st : State} :`,
		`  Code.getReturn (MLIR.runProgram Code.part${parts-1} st) ↔`,
		`  Code.getReturn (part${parts-1}_state st) := by`,
		`  unfold MLIR.runProgram; simp only`,
		`  unfold Code.part${parts-1}`,
		`  MLIR`,
		`  unfold part${parts-1}_state`,
		`  rfl`,
		``,
		`lemma part${parts-1}_updates_opaque {st : State} : `,
		`  Code.getReturn (part${parts-2}_state_update st) ↔`,
		`  Code.getReturn (part${parts-1}_state (part${parts-2}_state st)) := by`,
		`  simp [part${parts-2}_state_update, part${parts-1}_wp]`,
		``,
		`end Risc0.${funcName}.Constraints.WP`,
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
	const searchStart = stderr.indexOf(`${funcName}/Constraints/WeakestPresPart${part}.lean:`);
	const gammaIdx = stderr.indexOf("Γ", searchStart);
	const codeStart = stderr.indexOf("⟦", gammaIdx);
	return stderr.slice(gammaIdx+1, codeStart);
}

function extractStateTransformerLast(stderr: string, funcName: string, part: number): string {
	const searchStart = stderr.indexOf(`${funcName}/Constraints/WeakestPresPart${part}.lean:`);
	const startIdx = stderr.indexOf("Code.getReturn", searchStart) + "Code.getReturn".length;
	const endIdx = stderr.indexOf("↔", startIdx);
	return stderr.slice(startIdx, endIdx);
}
