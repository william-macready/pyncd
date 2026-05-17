from acset.instances import SStInstance, EntryRow


def test_sstinstance_empty():
    inst = SStInstance()
    assert inst.axis_sizes == {}
    assert inst.entries == []


def test_sstinstance_stores_entry():
    from data_structure.StrideCategory import RawAxis
    from data_structure.Numeric import Integer
    a, b = RawAxis.named('a'), RawAxis.named('b')
    inst = SStInstance(
        axis_sizes={a.uid: Integer(4), b.uid: Integer(6)},
        entries=[EntryRow(src=a.uid, tgt=b.uid, coeff=Integer(2))],
    )
    assert inst.axis_sizes[a.uid] == Integer(4)
    assert inst.entries[0].coeff == Integer(2)
