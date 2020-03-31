idp_home="/home/$USER/idp/usr/local/bin/idp"
data="/home/$USER/holygrail/experiments/02_AIJ/data/"
idp_files="/home/$USER/holygrail/experiments/02_AIJ/idp_files/"
results="/home/$USER/holygrail/experiments/02_AIJ/results/"
output="/home/$USER/holygrail/experiments/02_AIJ/output/"

${idp_home} "${idp_files}p12.idp" | grep -v "reduce" > "${output}p12.output.json"
${idp_home} "${idp_files}p13.idp" | grep -v "reduce" > "${output}p13.output.json"
${idp_home} "${idp_files}p16.idp" | grep -v "reduce" > "${output}p16.output.json"
${idp_home} "${idp_files}p17.idp" | grep -v "reduce" > "${output}p17.output.json"
${idp_home} "${idp_files}p18.idp" | grep -v "reduce" > "${output}p18.output.json"
${idp_home} "${idp_files}p19.idp" | grep -v "reduce" > "${output}p19.output.json"
${idp_home} "${idp_files}p20.idp" | grep -v "reduce" > "${output}p20.output.json"
${idp_home} "${idp_files}p25.idp" | grep -v "reduce" > "${output}p25.output.json"
${idp_home} "${idp_files}p93.idp" | grep -v "reduce" > "${output}p93.output.json"
${idp_home} "${idp_files}p5-split.idp" | grep -v "reduce" > "${output}p5-split.output.json"


