LoadPackage("smallsemi");


for n in [1..7] do
    filename := Concatenation("~/data/", PrintString(n), "elt_semis.txt");;
    fout := OutputTextFile(filename, false);;
    SetPrintFormattingStatus(fout, false);;

    total := NrSmallSemigroups(n);
    Print("Dumping ", total, " semigroups of order ", n, "...\n");;

    for ix in [1..total] do
        if RemInt(ix, 1000) = 0 then
            Print(QuoInt(ix,1000), "k\n");
        fi;
        table := RecoverMultiplicationTable(n,ix);;
        s := SmallSemigroup(n, ix);;
        first := 1;
        for row in table do
            if first = 0 then
                PrintTo(fout, ";");;
            fi;
            first := 0;
            for x in row do
                PrintTo(fout, x-1);
            od;
        od;
        # PrintTo(fout, " Gen");;
        # for g in MinimalGeneratingSet(s) do
        #     digit := Int(PrintString(g){[2..2]}) - 1;
        #     PrintTo(fout, digit);;
        # od;
        PrintTo(fout, "\n");;
    od;

    Print("done.\n");
od;