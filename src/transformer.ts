import * as IR from './IR';

export function generateUpdates(ir: IR.Statement[], drops: IR.DropFelt[]): string[] {
	let bufferWrites: Map<String, String> = new Map();
	let felts: Map<String, String> = new Map();
	let props: Map<String, String> = new Map();
	let updates: string[] = [];
	for (let i = 0; i < ir.length; ++i) {
		const statement = ir[i];
		switch (statement.kind) {
		case "assign":
			switch (statement.val.kind) {
			case "andEqz": {
				const expr = `(${
					props.get(statement.val.cond) ?? propVarName(statement.val.cond)
				} ∧ (${
					felts.get(statement.val.val) ?? feltVarName(statement.val.val)
				} = 0))`;
				props.set(statement.target, expr);
				updates.push(`[props][{name:=${statement.target}:PropVar}] ← ${expr}`);
			} break;
			case "binop":
				switch (statement.val.op) {
				case "Add": {
					const expr = `(${
						felts.get(statement.val.lhs) ?? feltVarName(statement.val.lhs)
					} + ${
						felts.get(statement.val.rhs) ?? feltVarName(statement.val.rhs)
					})`;
					felts.set(statement.target, expr);
					if (drops.every((d: IR.DropFelt) => d.val !== statement.target)) {
						updates.push(`[felts][{name:=${statement.target}:FeltVar}] ← ${expr}`);
					}
				} break;
				}
				break;
			case "get": {
				// TODO getOrRead
				const expr = bufferElementName(statement.val.bufferId, statement.val.back, statement.val.offset);
				felts.set(statement.target, expr)
				updates.push(`[${statement.target}] ←ₛ ${expr}`);
			} break;
			case "isz": {
				const expr = `(feltIsZero ${felts.get(statement.val.op) ?? feltVarName(statement.val.op)})`;
				felts.set(statement.target, expr);
				if (drops.every((d: IR.DropFelt) => d.val !== statement.target)) {
					updates.push(`[felts][{name:=${statement.target}:FeltVar}] ← ${expr}`);
				}
			} break;
			case "true": {
				props.set(statement.target, "True");
				updates.push(`[props][{name:=${statement.target}:PropVar}] ← True`);
			} break;
			}
			break;
		}
	}

	return updates;
}

function bufferElementName(name: string, back: string, offset: string): string {
	return `b_${name}_${back}_${offset}`;
}
function feltVarName(name: string): string {
	return name.replace("%", "f_");
}
function propVarName(name: string): string {
	return name.replace("%", "p_");
}
