#!/usr/bin/env python3
"""Render checked Lean dependencies. Requires Python 3 and Graphviz."""
from pathlib import Path
import collections
import json
import re
import subprocess
import textwrap

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
OUT = HERE / 'generated'
OUT.mkdir(exist_ok=True)
raw = {r['name']: r for r in json.loads((HERE / 'compiled_dependencies.json').read_text())}
source = json.loads((HERE / 'source_index.json').read_text())
records = {}
for name, record in source.items():
    matches = [name] if name in raw else [n for n in raw if n.endswith('.' + name)]
    if len(matches) != 1:
        raise ValueError(f'Expected one compiled declaration for {name}: {matches}')
    records[matches[0]] = dict(record, public_name=name)
raw_deps = {n: sorted(d for d in r['used'] if d in raw and d != n) for n, r in raw.items()}

# Labels select an expository overview. They never supply dependency edges.
friendly = {
    'Instance.optimum_eq_minimum': 'Attained offline optimum',
    'Instance.fifo_backlog_bound': 'FIFO backlog bound',
    'Instance.fifo_competitive': 'FIFO upper bound\nm + 1 − 1/m',
    'Instance.frontier_round_count_bound': 'Frontier progress',
    'SFFRounds.round_bounds': 'SFF round bounds',
    'SFFRounds.remaining_work_bound': 'SFF remaining work',
    'Instance.sffSchedule_known_optimum': 'SFF bound\n44 OPT²',
    'Instance.combinedSchedule_spec': 'Doubling and FIFO switch\n352 OPT min(m, OPT)',
    'Instance.combinedSchedule_nonclairvoyant': 'Combined algorithm causality',
    'exists_optimal_order_scheduler': 'Theorem 2\nOptimal-order causal scheduler',
    'Instance.record_batch_count': 'Logarithmic batch count',
    'Instance.batched_fifo_combined_bound': 'Theorem 4 · Upper bound\nFIFO on batched arrivals',
    'DeterministicScheduler.select_hidden_key': 'Deferred hidden-key choice',
    'LayeredPrefix.exists_recorded_forcing_forest': 'Finite adversarial forest',
    'LayeredPrefix.RecordedRun.forcing_layer_count': 'Layer-count bound',
    'LayeredPrefix.RecordedRun.optimum_bounds': 'General offline bounds\nL ≤ OPT ≤ 2L',
    'LayeredPrefix.RecordedRun.forcing_epoch_deficit': 'Forced idle capacity',
    'deterministic_competitive_lower': 'Theorem 1 · Deterministic\nGeneral lower bound',
    'StarChain.optimum_le_six': 'Star-chain offline schedule\nOPT ≤ 6',
    'StarChain.exists_type_consistent': 'Fixed star-chain adversary',
    'StarChain.block_has_idle': 'FIFO recurring idle slots',
    'fifo_constant_optimum_lower': 'Theorem 3\nFIFO lower bound at constant OPT',
    'BatchedAdversary.exists_balanced_layer_run': 'Balanced batched construction',
    'BatchedAdversary.optimum_eq': 'Batched exact optimum\nOPT = L',
    'BatchedAdversary.initial_record_credit': 'Passivity credit invariant',
    'BatchedAdversary.full_epoch_job_cutoffs': 'Per-job wide-service cutoffs',
    'BatchedAdversary.full_epoch_passivity': 'Aggregate passivity recurrence',
    'BatchedForcing.no_full_epoch': 'Geometric contradiction',
    'batched_competitive_lower': 'Theorem 4 · Deterministic\nBatched lower bound',
    'HardFamily.general_hard': 'Fixed general hard family',
    'HardFamily.batched_hard': 'Fixed batched hard family',
    'DeterministicScheduler.continuation_causal': 'Causal continuation after a prefix',
    'InstanceSequence.bad_persists': 'Later copies preserve bad flow',
    'FiniteAmplification.half_words_bad': 'Finite amplification\nAt least half the words are bad',
    'FiniteAmplification.exists_expected_large': 'Average over arbitrary random seeds',
    'HardFamily.expected_lower': 'One fixed input with large expected flow',
    'randomized_competitive_lower': 'Theorem 1 · Randomized\nGeneral lower bound',
    'randomized_batched_competitive_lower': 'Theorem 4 · Randomized\nBatched lower bound',
}
full = lambda n: 'Scheduling.' + n
overview = [full(n) for n in friendly]
assert set(overview) <= records.keys(), set(overview) - records.keys()
mains = {full(n) for n in [
    'deterministic_competitive_lower', 'randomized_competitive_lower',
    'exists_optimal_order_scheduler', 'fifo_constant_optimum_lower',
    'Instance.batched_fifo_combined_bound', 'batched_competitive_lower',
    'randomized_batched_competitive_lower']}


def closure(starts, adjacency):
    seen, todo = set(starts), list(starts)
    while todo:
        for dep in adjacency.get(todo.pop(), []):
            if dep not in seen:
                seen.add(dep)
                todo.append(dep)
    return seen


def displayed_dependencies(selected):
    """Nearest displayed prerequisites through omitted compiled helpers."""
    selected = set(selected)
    edges, witnesses = set(), {}
    for target in sorted(selected):
        queue = collections.deque((d, [target, d]) for d in raw_deps.get(target, []))
        seen = {target}
        while queue:
            dep, path = queue.popleft()
            if dep in seen:
                continue
            seen.add(dep)
            if dep in selected:
                edges.add((dep, target))
                witnesses[(dep, target)] = list(reversed(path))
            else:
                queue.extend((d, path + [d]) for d in raw_deps.get(dep, []) if d not in seen)
    return edges, witnesses


def reduce_edges(nodes, edges):
    adjacency = {n: [] for n in nodes}
    indegree = dict.fromkeys(nodes, 0)
    for a, b in sorted(edges):
        adjacency[a].append(b)
        indegree[b] += 1
    todo = [n for n in nodes if not indegree[n]]
    visited = 0
    while todo:
        n = todo.pop()
        visited += 1
        for b in adjacency[n]:
            indegree[b] -= 1
            if not indegree[b]:
                todo.append(b)
    if visited != len(nodes):
        return edges, False
    retained = set()
    for a, b in edges:
        alternatives = [d for d in adjacency[a] if d != b]
        if b not in closure(alternatives, adjacency):
            retained.add((a, b))
    return retained, True


ids = {n: 'decl_' + str(i) for i, n in enumerate(sorted(records))}
nodes = {}
for name, record in records.items():
    short = record['public_name'].removeprefix('Scheduling.')
    nodes[ids[name]] = {
        'id': ids[name], 'name': name, 'label': friendly.get(short, short),
        'kind': 'theorem' if raw[name]['kind'] == 'theorem' else 'definition',
        'statement': raw[name]['statement'], 'file': record['file'], 'line': record['line'],
        'source': record['source'], 'checked': True,
    }


def ancestors(*names):
    return sorted(set(records) & closure([full(n) for n in names], raw_deps))


views = {
    'overview': ('Main results overview', overview),
    'upper': ('Upper bounds: FIFO, SFF and combined scheduler', ancestors(
        'exists_optimal_order_scheduler', 'Instance.batched_fifo_combined_bound')),
    'general': ('General deterministic lower bound', ancestors('deterministic_competitive_lower')),
    'fifo': ('Constant-OPT FIFO lower bound', ancestors('fifo_constant_optimum_lower')),
    'batched': ('Batched deterministic lower bound', ancestors('batched_competitive_lower')),
    'randomized': ('Randomized amplification and composition', sorted(n for n, r in records.items()
        if Path(r['file']).stem in {'FiniteForests', 'HardFamilies', 'AppendInstance',
            'AppendRestriction', 'AppendObservation', 'AppendBefore', 'AppendContinuation',
            'HardContinuation', 'InstanceSequence', 'FiniteAmplification', 'Randomized',
            'RandomizedFamily', 'RandomizedLower'})),
    'full': ('All source declarations', sorted(records)),
}
graph_data = {}
for key, (title, chosen) in views.items():
    edges, paths = displayed_dependencies(chosen)
    edges, acyclic = reduce_edges(chosen, edges)
    edge_list = [{'from': ids[a], 'to': ids[b], 'path': paths[(a, b)]} for a, b in sorted(edges)]
    lines = ['digraph proof {',
        'graph [rankdir=TB,bgcolor="white",pad="0.2",nodesep="0.25",ranksep="0.55",splines=polyline,outputorder=edgesfirst];',
        'node [fontname="Helvetica",fontsize=10,style=filled,fillcolor="#b9e5b2",color="#23823c",fontcolor="#133b1e",penwidth=1.3,margin="0.13,0.08"];',
        'edge [color="#748076",arrowsize=0.65,penwidth=0.8];']
    if key == 'overview':
        lines.append('graph [pack=true,packmode="array_u2"];')
    for n in sorted(chosen):
        d = nodes[ids[n]]
        label = d['label'] if key == 'overview' else records[n]['public_name'].removeprefix('Scheduling.')
        label = '\n'.join('\n'.join(textwrap.wrap(part, width=35, break_long_words=True,
            break_on_hyphens=False)) for part in label.split('\n'))
        attrs = {'id': d['id'], 'label': label,
            'shape': 'ellipse' if d['kind'] == 'theorem' else 'box', 'tooltip': n + ' — Lean-checked'}
        if n in mains:
            attrs.update(penwidth='2.5', peripheries='2', fillcolor='#8fd18b', fontsize='12')
        lines.append(json.dumps(n) + ' [' + ','.join(k + '=' + json.dumps(v, ensure_ascii=False)
            for k, v in attrs.items()) + '];')
    lines.extend(json.dumps(a) + ' -> ' + json.dumps(b) + ';' for a, b in sorted(edges))
    lines.append('}')
    dot, svg = OUT / (key + '.dot'), OUT / (key + '.svg')
    dot.write_text('\n'.join(lines))
    subprocess.run(['dot', '-Tsvg', str(dot), '-o', str(svg)], check=True)
    graph_data[key] = {'title': title, 'nodes': [ids[n] for n in sorted(chosen)],
        'edges': edge_list, 'acyclic': acyclic,
        'svg': re.sub(r'^.*?(?=<svg\s)', '', svg.read_text(), flags=re.S)}

# Module imports are a separate graph, never substituted for proof dependencies.
modules = {}
for p in sorted((ROOT / 'Scheduling').glob('*.lean')):
    name = 'Scheduling.' + p.stem
    modules[name] = re.findall(r'^import\s+(Scheduling(?:\.\w+)*)\b', p.read_text(), re.M)
module_edges = sorted((dep, target) for target, deps in modules.items() for dep in deps if dep in modules)
(OUT / 'module_imports.json').write_text(json.dumps({'modules': modules, 'edges': module_edges}, indent=2))
module_dot = ['digraph modules {', 'rankdir=LR;', 'node [shape=box,fontname="Helvetica",fontsize=10];']
module_dot += [json.dumps(n) + ' [label=' + json.dumps(n.removeprefix('Scheduling.')) + '];' for n in modules]
module_dot += [json.dumps(a) + ' -> ' + json.dumps(b) + ';' for a, b in module_edges]
(OUT / 'modules.dot').write_text('\n'.join(module_dot + ['}']))
subprocess.run(['dot', '-Tsvg', str(OUT / 'modules.dot'), '-o', str(OUT / 'modules.svg')], check=True)

data = {'nodes': nodes, 'views': graph_data, 'main': [ids[n] for n in sorted(mains)],
    'audit_count': (ROOT / 'Audit.lean').read_text().count('#print axioms'),
    'extraction': 'Lean 4.33.0 compiled types and values; omitted project helpers traversed; transitive redundant arrows removed in acyclic views.',
    'raw_declaration_count': len(raw), 'source_declaration_count': len(records),
    'foundational_axioms': ['propext', 'Classical.choice', 'Quot.sound']}
(OUT / 'graph_data.json').write_text(json.dumps(data, ensure_ascii=False, indent=2))
payload = json.dumps(data, ensure_ascii=False).replace('</', '<\\/')
(OUT / 'Nonclairvoyant_Scheduling_Blueprint.html').write_text(
    (HERE / 'template.html').read_text().replace('__GRAPH_DATA__', payload))
for fmt in ['pdf', 'png']:
    subprocess.run(['dot', '-T' + fmt, '-Gdpi=100', str(OUT / 'overview.dot'), '-o',
        str(OUT / ('Nonclairvoyant_Scheduling_Dependency_Graph.' + fmt))], check=True)
(OUT / 'Nonclairvoyant_Scheduling_Dependency_Graph.svg').write_text((OUT / 'overview.svg').read_text())
print(json.dumps({'source_nodes': len(records), 'compiled_declarations': len(raw),
    'views': {k: {'nodes': len(v['nodes']), 'edges': len(v['edges']), 'acyclic': v['acyclic']}
        for k, v in graph_data.items()}, 'module_nodes': len(modules), 'module_edges': len(module_edges)}, indent=2))
