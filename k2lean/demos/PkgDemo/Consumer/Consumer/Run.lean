import Consumer.Hooks
import ParamsBench.Main

/-! The run executable: the generated driver, which takes the library's parameters (PKG-6), at the
user's implementation. -/

def main (args : List String) : IO UInt32 := @ParamsBench.benchMain Consumer.hooks args
