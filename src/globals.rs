#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GlobalSymbol {
    sym: u32,
}

impl GlobalSymbol {
    const fn new(sym: u32) -> Self {
        GlobalSymbol { sym }
    }

    pub fn sym(&self) -> u32 {
        self.sym
    }

    pub fn index(&self) -> usize {
        self.sym as usize
    }
}

pub const FALSE: GlobalSymbol = GlobalSymbol::new(0);
pub const TRUE: GlobalSymbol = GlobalSymbol::new(1);
pub const IMP: GlobalSymbol = GlobalSymbol::new(2);
pub const AND: GlobalSymbol = GlobalSymbol::new(3);
pub const OR: GlobalSymbol = GlobalSymbol::new(4);
pub const NOT: GlobalSymbol = GlobalSymbol::new(5);
pub const EQ: GlobalSymbol = GlobalSymbol::new(6);
pub const NAT: GlobalSymbol = GlobalSymbol::new(7);
pub const ADD: GlobalSymbol = GlobalSymbol::new(8);
pub const MUL: GlobalSymbol = GlobalSymbol::new(9);
pub const PRELUDE_MAX: usize = 10;

pub struct Globals {
    globals: Vec<GlobalInfo>,
}

#[derive(Clone)]
struct GlobalInfo {
    arity: u32,
    name: String,
}

impl Default for Globals {
    fn default() -> Self {
        let mut globals = vec![
            GlobalInfo {
                arity: 0,
                name: String::new()
            };
            PRELUDE_MAX
        ];
        globals[FALSE.index()] = GlobalInfo {
            arity: 0,
            name: "false".to_owned(),
        };
        globals[TRUE.index()] = GlobalInfo {
            arity: 0,
            name: "true".to_owned(),
        };
        globals[IMP.index()] = GlobalInfo {
            arity: 2,
            name: "imp".to_owned(),
        };
        globals[AND.index()] = GlobalInfo {
            arity: 2,
            name: "and".to_owned(),
        };
        globals[OR.index()] = GlobalInfo {
            arity: 2,
            name: "or".to_owned(),
        };
        globals[NOT.index()] = GlobalInfo {
            arity: 1,
            name: "not".to_owned(),
        };
        globals[EQ.index()] = GlobalInfo {
            arity: 2,
            name: "eq".to_owned(),
        };
        globals[NAT.index()] = GlobalInfo {
            arity: 1,
            name: "nat".to_owned(),
        };
        globals[ADD.index()] = GlobalInfo {
            arity: 2,
            name: "add".to_owned(),
        };
        globals[MUL.index()] = GlobalInfo {
            arity: 2,
            name: "mul".to_owned(),
        };
        Globals { globals }
    }
}

impl Globals {
    pub fn global(&self, sym: u32) -> GlobalSymbol {
        if sym < self.count() {
            GlobalSymbol { sym }
        } else {
            panic!("Global out of range");
        }
    }

    pub fn count(&self) -> u32 {
        self.globals.len() as u32
    }

    pub fn get_arity(&self, sym: GlobalSymbol) -> u32 {
        self.globals[sym.index()].arity
    }

    pub fn get_name(&self, sym: GlobalSymbol) -> &str {
        &self.globals[sym.index()].name
    }
}
