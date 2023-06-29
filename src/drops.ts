import { DataLocEq, IR, irLinesToLean } from "./IR";

export function createWitnessCodeWithDropsLean(funcName: string, ir: IR.Statement[], linesPerPart: number): string {
	const irWithDrops = insertDrops(ir, linesPerPart);

	return [
		`import Risc0.Gadgets.${funcName}.Witness.CodeReordered`,
		"",
		`namespace Risc0.${funcName}.Witness.Code`,
		"",
		"open MLIRNotation",
		"def full_opt : MLIRProgram :=",
		irLinesToLean(irWithDrops),
		"end Risc0.ComputeDecode.Witness.Code",
	].join("\n");
}

function insertDrops(ir: IR.Statement[], linesPerPart: number): IR.Statement[] {
	let retIR = ir.slice(0);
	const dropLocations = calculateDropPoints(ir);
	console.log (`${ir.length} ${dropLocations.size} ${[...dropLocations.values()].length}`);
	const locs = [...dropLocations.values()].sort((a, b) => a - b).reverse();
	locs.forEach(loc => {
		const [feltToDrop, _] = [...dropLocations.entries()].find(([val, pos]) => pos === loc)!;
		let insertLoc = Math.ceil(loc/linesPerPart)*linesPerPart;
		let instr = new IR.DropFelt(feltToDrop, false);
		if (insertLoc > retIR.length) {
			retIR.push(instr);
		} else {
			retIR = [
				...retIR.slice(0, insertLoc),
				instr,
				...retIR.slice(insertLoc)
			];
		}
	})
	return retIR;
}

function calculateDropPoints(ir: IR.Statement[]): Map<string, number> {
	let dropPoints: Map<string, number> = new Map();
	for (let i = 0; i < ir.length; ++i) {
		const statement = ir[i];
		statement.creates().filter(c => c.kind === "felt").map(created => {
			// Reverse a list of the statements after this one so we can use findIndex
			const laterStatements = ir.slice(i).reverse();
			const lastUseRevIdx = laterStatements.findIndex(stmt => stmt.uses().some(u => DataLocEq(u, created)));
			const dropIdx = ir.length - lastUseRevIdx;
			if (dropPoints.has(created.idx)) {
				console.log(`DUP ${created.idx}`);
			}
			dropPoints.set(created.idx, dropIdx);
			// console.log(`${created.idx} created at ${i} dropped at ${dropIdx}`);
		})
	}
	return dropPoints;
}