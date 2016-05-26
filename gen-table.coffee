fs = require 'fs'
child = require 'child_process'
assert = require 'assert'

THRESHOLD = 300

e = child.execSync

instances = fs.readdirSync './instances'

execs = ["solver"]
execst = ["pico"].concat(execs.map( (s) -> if s is "solver" then "mine" else s))

e("make")

PADDING = 15

pad = (s, n = PADDING) ->
    s += " " for i in [s.length...n]
    s

nl = -> process.stdout.write("\n")
write = (ss...) ->
    process.stdout.write(pad(s + "")) for s in ss
    { nl }

write("Test")
for attr in ["Time", "Props/Sec", "Decisions"]
    write("#{attr}_#{exec}") for exec in execst
write("Sat?")

nl()

normalize = (x, d=3) -> Math.round(x*Math.pow(10,d))/Math.pow(10,d)

for instance in instances when Number(instance.match(/^vars-(\d{3})-.*\.cnf$/)[1]) <= THRESHOLD
    write(instance[instance.indexOf("-")+1...instance.indexOf('.')])

    statsSet = []
    time = null
    try
        e "timer -n picosat -n -v -o stats.txt < instances/#{instance} 2>time.txt", { encoding: 'utf-8' }
    catch err

    stats = fs.readFileSync "./stats.txt", "utf-8"
    time = normalize JSON.parse(fs.readFileSync "./time.txt", "utf-8").elapsed/1e6

    decisions = stats.match(/c (\d*) decisions/)[1]
    propagations = stats.match(/c (\d*) propagations/)[1]
    #time = stats.match(/c (.*) seconds in library/)[1]
    satisfiable = stats.match(/s ([A-Z]+)\n/)[1] is "SATISFIABLE"

    statsSet.push { decisions, propagations: propagations//time, time: time + "s" }

    for exec in execs
        try
            e("timer -n ./#{exec} < instances/#{instance} > stats.txt 2>time.txt", { enconding: "utf-8" })
        catch err

        time = normalize JSON.parse(fs.readFileSync "./time.txt", "utf-8").elapsed/1e6

        stats = fs.readFileSync "./stats.txt", "utf-8"
        stats = JSON.parse(stats)

        assert(stats.satisfiable is satisfiable)

        statsSet.push { time: time + "s", propagations: Math.floor(stats["propagations/sec"]), decisions: stats.decisions }

    for attr in ["time", "propagations", "decisions"]
        for stats in statsSet
            write(stats[attr])

    write(if satisfiable then "sat" else "unsat")
    nl()

e("rm -f ./stats.txt")
e("rm -f ./time.txt")