fs = require 'fs'
child = require 'child_process'

THRESHOLD = 200

e = child.execSync

instances = fs.readdirSync './instances'

#e("make")

for instance in instances when Number(instance.match(/^vars-(\d{3})-.*\.cnf$/)[1]) <= THRESHOLD
    try
        e("./solver < instances/#{instance} > /dev/null")
    catch err

    #stats = fs.readFileSync "./stats.txt", "utf-8"

    #console.log instance
    #console.log "------------------"
    #console.log stats

#e("rm -f ./stats.txt")
