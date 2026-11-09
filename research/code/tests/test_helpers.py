"""The thin helper module `table` (CSV writer)."""
import csv

import table


def test_table_write_roundtrips(tmp_path):
    rows = [{"beta": 1.0, "K": 0.21}, {"beta": 2.0, "K": 0.30}]
    path = tmp_path / "t.csv"
    table.write(str(path), rows, ["beta", "K"])
    with open(path) as f:
        got = list(csv.DictReader(f))
    assert [r["beta"] for r in got] == ["1.0", "2.0"]
    assert [r["K"] for r in got] == ["0.21", "0.3"]
