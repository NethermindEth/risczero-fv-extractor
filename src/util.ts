import fs from 'fs';

export function addToImportFile(prefix: string, pathToImport: string) {
	let importFile = fs.readFileSync(`${prefix}/Risc0.lean`, { encoding: "utf8" });
	const importLine = `import Risc0.Gadgets.${pathToImport}`;
	importFile = importFile.split("\n").map(line => line === `-- ${importLine}`? importLine : line).join("\n");
	if (!importFile.includes(importLine)) {
		importFile = `${importFile}\n${importLine}`;
	}
	fs.writeFileSync(`${prefix}/Risc0.lean`, importFile, { encoding: "utf8" });
}

export function commentInImportFile(prefix: string, predicate: (line: string) => boolean): string[] {
	const importFileBefore = fs.readFileSync(`${prefix}/Risc0.lean`, { encoding: "utf8" }).split("\n");
	const importFileAfter = importFileBefore.map(line => !line.trim().startsWith("--") && predicate(line) ? `-- ${line}` : line);
	const changedLines = importFileAfter.filter(line => !importFileBefore.includes(line));
	fs.writeFileSync(`${prefix}/Risc0.lean`, importFileAfter.join("\n"), { encoding: "utf8" });
	return changedLines
}

export function uncommentInImportFile(prefix: string, predicate: (line: string) => boolean): string[] {
	const importFileBefore = fs.readFileSync(`${prefix}/Risc0.lean`, { encoding: "utf8" }).split("\n");
	const importFileAfter = importFileBefore.map(line => line.trim().startsWith("--") && predicate(line) ? line.trim().slice(2).trim() : line);
	const changedLines = importFileAfter.filter(line => !importFileBefore.includes(line));
	fs.writeFileSync(`${prefix}/Risc0.lean`, importFileAfter.join("\n"), { encoding: "utf8" });
	return changedLines
}

export type BufferConfig = {
	inputs: [string, number][],
	outputs: [string, number][],
};
