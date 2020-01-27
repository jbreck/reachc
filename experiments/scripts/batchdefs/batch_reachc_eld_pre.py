import choraconfig, glob, os.path

batch = choraconfig.clone_batch("reachc_spacergt")


batch["root"] = os.path.join(choraconfig.get_tool_root("reachc"), "experiments/benchmarks/eld_pre")
batch["files"] = glob.glob(batch["root"] + "/*.smt2")
batch["toolIDs"] = ["reachc",
                    #"reachc_refine",
                    #"spacer471"
                   ]
batch["timeout"] = 300
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
