import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

#chc-comp19/lia-lin
#batch["root"] = os.path.join(choraconfig.get_tool_root("reachc"), "experiments/benchmarks/small/")
batch["root"] = os.path.join(choraconfig.get_tool_root("reachc"), "experiments/benchmarks/chc-comp19/")
batch["files"] = glob.glob(batch["root"] + "lia-lin/*.smt2") + glob.glob(batch["root"] + "lia-nonlin/*.smt2") 
batch["format_style"] = "assert"
batch["toolIDs"] = ["reachc","spacer471"]
#batch["format_col_width_proportional"] = True
batch["timeout"] = 30

