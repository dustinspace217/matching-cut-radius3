try:
    import pysat
    print("pysat OK", pysat.__file__)
except Exception as e:
    print("pysat NO", e)
import shutil
for t in ("minisat", "cryptominisat", "picosat", "cadical", "kissat", "glucose", "z3"):
    print(t, shutil.which(t))
