import traceback

def func(c):
    for i in c:
        pass

def method(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)

def method2(cmd):
    print("====call stack end====")
    traceback.print_stack()
    print("====call stack end====")
    exec(cmd)    

class Cls:
    def __init__(self, cmd, max=0):
        self.max = max
        self.cmd = cmd

    def __iter__(self):
        method(self.cmd)
        self.n = 0
        return self
    
    def __next__(self):
        method2(self.cmd)
        if self.n > self.max:
            raise StopIteration
        self.n += 1
        return self.n
    
def main_1():
    cmd = "print('Method in method')"
    print("have_iter")
    func(Cls(cmd, 4)) 

def main_2():
    cmd = "print('Method in method')"
    print("have_not_iter")
    Cls(cmd, 4)

if __name__ == "__main__":
    main_1()
    main_2()