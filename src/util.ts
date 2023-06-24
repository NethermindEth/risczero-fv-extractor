import fs from 'fs';

export function addToImportFile(prefix: string, pathToImport: string) {
	let importFile = fs.readFileSync(`${prefix}/Risc0.lean`, { encoding: "utf8" });
	const importLine = `import Risc0.Gadgets.${pathToImport}`;
	if (!importFile.includes(importLine)) {
		importFile = `${importFile}\n${importLine}`;
	}
	fs.writeFileSync(`${prefix}/Risc0.lean`, importFile, { encoding: "utf8" });
}