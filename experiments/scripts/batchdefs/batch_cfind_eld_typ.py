import choraconfig, glob, os.path

batch = choraconfig.clone_batch("cfind_spacergt")


batch["root"] = os.path.join(choraconfig.get_tool_root("cfind"), "experiments/benchmarks/eld_typ")
batch["files"] = glob.glob(batch["root"] + "/*.smt2")
batch["toolIDs"] = ["cfind",
                    #"cfind_refine",
                    #"spacer471"
                   ]
batch["timeout"] = 300
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
