fs = require 'fs'
child = require 'child_process'

THRESHOLD = 300

e = child.execSync

instances = fs.readdirSync './instances'

execs = ["solver", "llop-solver", "necavit-solver", "arnsangra-solver"]

e("make")

for instance in instances when Number(instance.match(/^vars-(\d{3})-.*\.cnf$/)[1]) <= THRESHOLD
    console.log instance
    console.log "#####################"

    try
        e "picosat -n -v -o stats.txt < instances/#{instance}"
    catch err

    stats = fs.readFileSync "./stats.txt", "utf-8"

    decisions = stats.match(/c (\d*) decisions/)[1]
    propagations = stats.match(/c (\d*) propagations/)[1]
    time = stats.match(/c (.*) seconds in library/)[1]
    satisfiable = if stats.match(/s ([A-Z]+)\n/)[1] is "SATISFIABLE" then "true" else "false"

    console.log "picosat          { \"time\": #{time}, \"decisions\": #{decisions}, \"propagations/sec\": #{Math.round((Number(propagations)/Number(time))*1000)/1000}, \"satisfiable\": #{satisfiable} }"
    console.log "-----------------"

    for exec in execs
        try
            e("./#{exec} < instances/#{instance} > stats.txt")
        catch err

        stats = fs.readFileSync "./stats.txt", "utf-8"

        exec += " " while exec.length < 16
        console.log "#{exec} #{stats[0..-2]}"
        console.log "-----------------"


e("rm -f ./stats.txt")
