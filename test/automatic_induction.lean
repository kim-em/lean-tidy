import tidy.automatic_induction
import tidy.pempty

def f (x : pempty) : false := begin automatic_induction, end

def g (x : fin 0) : false := begin automatic_induction, automatic_induction, end