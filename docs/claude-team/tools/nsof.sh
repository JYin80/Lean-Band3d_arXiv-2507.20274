# Usage (run from $HOME/mnt/RBM3D): bash docs/claude-team/tools/nsof.sh name1 name2 ...
# Prints the full name (namespace.name) and file:line of each declaration in RBM3D/ (outside Probe/). Caveats: does not parse `inductive`; a file that reopens a nested namespace (e.g. ends with an `...Inst` namespace) can be misreported: confirm with grep.
ns(){ awk -v L="$2" 'NR<=L && /^namespace /{s[++n]=$2} NR<=L && /^end /{ if(n>0 && $2==s[n]) n--} END{o="";for(i=1;i<=n;i++)o=o (i>1?".":"") s[i]; print o}' "$1"; }
for n in "$@"; do
  hit=$(grep -rn --include=*.lean -E "^(private )?(noncomputable )?(theorem|def|abbrev|lemma|structure) ${n}( |$)" RBM3D | grep -v Probe | head -1)
  if [ -z "$hit" ]; then echo "$n: NOT FOUND"; continue; fi
  f=${hit%%:*}; rest=${hit#*:}; l=${rest%%:*}; p=$(echo "$rest" | grep -o "private" | head -1)
  echo "$n: $(ns $f $l).$n  $f:$l $p"
done
