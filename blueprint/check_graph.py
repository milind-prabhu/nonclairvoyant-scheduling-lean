#!/usr/bin/env python3
"""Check source coverage, SVG nodes, and every displayed dependency witness."""
from pathlib import Path
import json
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
raw = {r['name']: r for r in json.loads((HERE / 'compiled_dependencies.json').read_text())}
source = json.loads((HERE / 'source_index.json').read_text())
data = json.loads((HERE / 'generated/graph_data.json').read_text())
nodes = data['nodes']
assert len(nodes) == len(source) == data['source_declaration_count']
assert {n['name'] for n in nodes.values()} <= raw.keys()
assert all(n['statement'] for n in nodes.values()), 'Missing Lean statement'
count = 0
for key, view in data['views'].items():
    svg = ET.fromstring(view['svg'])
    svg_nodes = {e.attrib['id'] for e in svg.iter() if e.attrib.get('class') == 'node'}
    assert svg_nodes == set(view['nodes']), (key, 'SVG node mismatch')
    for edge in view['edges']:
        path = edge['path']
        assert path[0] == nodes[edge['from']]['name']
        assert path[-1] == nodes[edge['to']]['name']
        assert edge['from'] in svg_nodes and edge['to'] in svg_nodes
        for prerequisite, result in zip(path, path[1:]):
            assert prerequisite in raw[result]['used'], (key, prerequisite, result)
        count += 1
assert set(data['views']['full']['nodes']) == set(nodes)
print(f'Graph check passed: {len(nodes)} source declarations, {len(data["views"])} views, '
      f'{count} displayed arrows with compiled dependency witnesses.')
