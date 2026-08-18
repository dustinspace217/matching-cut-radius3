#!/usr/bin/env python3
"""Extract the reviewer subagent's final assistant text from its
transcript jsonl (the report it composed but never delivered)."""
import json

path = ("/home/dustin/.claude/projects/-home-dustin-Claude-p-vs-np/"
        "00235758-54d9-4aeb-a4e5-6eb582f4b131/subagents/"
        "agent-ablock9-reviewer-052fab5a2aa4343e.jsonl")
texts = []
with open(path) as f:
    for line in f:
        try:
            m = json.loads(line)
        except json.JSONDecodeError:
            continue
        if m.get("type") != "assistant":
            continue
        for b in m.get("message", {}).get("content", []):
            if isinstance(b, dict) and b.get("type") == "text":
                t = b.get("text", "")
                if t.strip():
                    texts.append(t)
print(f"--- {len(texts)} assistant text blocks; LAST one below ---")
print(texts[-1] if texts else "NO TEXT FOUND")
