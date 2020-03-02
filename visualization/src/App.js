import React from "react";
import "./App.css";
import * as R from "ramda";
import ReactDOM from "react-dom";

var steps;
var vocabulary;

// String constants used in the file

const sol = "Solution!";
const bijectivity = "Bijectivity";
const logigramConstraint = "Logigram Constraint";
const transitivity = "Transitivity constraint";
const combinationConstraints = "Combination of logigram constraints";
const logicon = "Logigram constraints";

const legend = "Legend";
const legend_new_fact = "New fact";
const legend_derived_fact = "Known fact";
const legend_false = "False";
const legend_true = "True";
const legend_contradiction = "Contradiction Fact"

const initialState = {
  clue: null,
  known: [],
  derived: [],
  assumptions: []
};

function nestedReducer(state, next){
  return {
    clue: next.clue,
    known: [...state.known, ...state.derived],
    derived: next.derivations,
    assumptions: next.assumptions,
  };
}   

function sequenceReduce(state, next){

  const nestedSequenceInitialState = {
    clue: null,
    known: state.known == null ? [] : state.known,
    derived: [],
    assumptions: []
  }

  return {
    fact: next.derivable_fact,
    known:state.known,
    reason_sequence: next.reason_sequence != null ? R.scan(nestedReducer, nestedSequenceInitialState, next.reason_sequence).slice(1) : null
  }
}  

function reducer(state, next) {

  const reasonSequenceInitialState = {
    fact:null,
    reason_sequence: [],
    known: next.assumptions
  } 

  return {
    clue: next.clue,
    known: [...state.known, ...state.derived],
    derived: next.derivations,
    assumptions: next.assumptions,
    nested_explanations: Array.isArray(next.nested_explanations) ? R.scan(sequenceReduce, reasonSequenceInitialState,next.nested_explanations).slice(1): null
  };
}

function cleanedFacts(steps) {
  const factsOverTime = R.scan(reducer, initialState, steps);
  return factsOverTime.filter(facts =>
    facts.derived.some(
      knowledge =>
        getKnowledgeFrom(facts.known, knowledge.subject, knowledge.object) ==
        null
    )
  );
}

function getKnowledgeFrom(inArray, entity1, entity2) {
  return inArray.find(matches(entity1, entity2));
}

function matches(entity1, entity2) {
  return fact => {
    if (fact.subject === entity1 && fact.object === entity2) {
      return true;
    }
    if (fact.object === entity1 && fact.subject === entity2) {
      return true;
    }
    return false;
  };
}

const size = 32;
const styles = {
  parentGrid: (nbEntities, nbTypes) => ({
    display: "grid",
    width: nbEntities * nbTypes * size,
    height: nbEntities * nbTypes * size,
    "grid-template-columns": `auto `.repeat(nbTypes)
  }),
  parentGridItem: nbEntities => ({
    width: size * nbEntities - 2,
    height: size * nbEntities - 2,
    border: "1px solid black"
  }),
  parentGridItemVoc: (nbEntities, vertical) => ({
    ...styles.parentGridItem(nbEntities),
    "background-color": "whitesmoke",
    color: "black",
    display: "grid",
    "grid-template-columns": `auto `.repeat(vertical ? nbEntities : 1),
    "flex-direction": vertical ? "row" : "column"
  }),
  childVocGridItem: (nbEntities, vertical) => ({
    border: "1px dashed black",
    display: "flex",
    "align-items": "center",
    "justify-content": "center",
    ...(vertical
      ? {
          "writing-mode": "vertical-lr",
          width: size - 2,
          height: size * nbEntities - 2
        }
      : {
          width: size * nbEntities - 2,
          height: size - 2
        })
  }),
  parentGridItemEmpty: nbEntities => ({
    width: nbEntities * size,
    height: nbEntities * size
  }),
  parentGridItemFill: nbEntities => ({
    ...styles.parentGridItem(nbEntities),
    display: "grid",
    "grid-template-columns": `auto `.repeat(nbEntities)
  }),
  childFillGridItem: (color, frontcolor) => ({
    width: size - 2,
    height: size - 2,
    border: "1px dashed black",
    display: "flex",
    "align-items": "center",
    "justify-content": "center",
    "background-color": color,
    color: frontcolor
  }),
  childNestedButtonItem:(color, frontcolor) => ({
    width: size - 2,
    height: size - 2,
    border: "5px solid black",
    display: "flex",
    "align-items": "center",
    "justify-content": "center",
    "background-color": color,
    color: frontcolor
  })
};

function cleanClues(steps) {
  const clues = steps.map(element => element.clue);
  const uniqueclues = clues
    .filter(function(item, pos) {
      return clues.indexOf(item) === pos;
    })
    .filter(function(el) {
      return (
        [
          bijectivity,
          logigramConstraint,
          transitivity,
          combinationConstraints,
          logicon
        ].indexOf(el) < 0
      );
    });

  for (var i = uniqueclues.length - 1; i >= 0; i--) {
    if (uniqueclues[i] === logicon || uniqueclues[i] === sol) {
      uniqueclues.splice(i, 1);
    }
  }

  uniqueclues.push(bijectivity);
  uniqueclues.push(transitivity);
  uniqueclues.push(combinationConstraints);

  return uniqueclues;
}

function App({ problemName }) {
  // input files
  
  steps = require(`./source_explanations/${problemName}.output.json`);
  vocabulary = require(`./source_explanations/${problemName}.voc.json`);

  const clues = cleanClues(steps);

  // state variables: whenever they are updated, the hooks back to this place => update interface
  const [index, setIndex] = React.useState(0);
  const [sequenceIndex, setSequenceIndex] = React.useState(0)
  // const [activeSequenceIndex, setActiveSequenceIndex] = React.useState(0)
  const [nestedIndex, setNestedIndex] = React.useState(0)

  const factsOverTime = React.useMemo(() => {
    return cleanedFacts(steps);
  }, []);


  function setSequenceIndexClipped(newIndex, maxVal){
    // setNestedIndex(0)
    if (newIndex > maxVal) {
      setSequenceIndex(maxVal);
    } else if (newIndex < 0) {
      setSequenceIndex(0);
    } else {
      setSequenceIndex(newIndex);
    }
  }

 function setIndexClipped(newIndex) {
    setNestedIndex(-1)
    setSequenceIndex(-1)
    if (newIndex >= factsOverTime.length) {
      setIndex(factsOverTime.length);
    } else if (newIndex < 0) {
      setIndex(0);
    } else {
      setIndex(newIndex);
    }
  }

  function setNestedIndexClipped(newIndex, maxLength) {

    if (newIndex > maxLength) {
      setNestedIndex(maxLength);
    } else if (newIndex < 0) {
      setNestedIndex(0);
    } else {
      setNestedIndex(newIndex);
    }
  }

  let facts = null
  let usedClue

  if(nestedIndex > 0){
    facts = factsOverTime[index-1];
    usedClue = <UsedClue clues={clues} clue={facts.nested_explanations[sequenceIndex-1].reason_sequence[nestedIndex-1].clue} />
  }else if(index > 0){
    facts = factsOverTime[index-1];
    usedClue = <UsedClue clues={clues} clue={facts.clue} />
  }else{
    usedClue = <UsedClue clues={clues} clue={null} />
  }

   
  ReactDOM.render(
    <div className="Clues">
      <h2><span class="line-center">Clues</span></h2>
      {usedClue}
      <Legend />
      <p></p>
    </div>
    ,document.getElementById("clues"));

  const header = (<h2><span className="line-center">Puzzle</span></h2>);
  
  let prevNextButton;
  let prevNextSequenceButton = null
  let counterfact = null

  if( facts === null){
    prevNextButton = <div><button onClick={() => setIndexClipped(index + 1)}>start</button></div>
  }else if(Array.isArray(facts.nested_explanations) && facts.nested_explanations[0].derivable_fact != null  ){

    prevNextButton = <div>
          <table>
          <td><button onClick={() => setIndexClipped(index - 1)}>&#8592; Prev</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button className="heavyBorder" onClick={() => setSequenceIndex(1)}><span  role="img"  aria-label="help">&#x1F4A1; - HELP</span></button></td>
            <td className="buttonNavigationClues"></td>
            <td><button onClick={() => setIndexClipped(index + 1)}>Next &#8594;</button></td>

          </table> 
        </div>  
    
    const nested_explanations = facts.nested_explanations.filter((nExpl) => nExpl.fact != null)
    
    if(sequenceIndex > 0 && nestedIndex > 0){

      counterfact = JSON.parse(JSON.stringify(nested_explanations[sequenceIndex-1].fact))
      counterfact.value = ~counterfact.value

      facts=nested_explanations[sequenceIndex-1].reason_sequence.filter((nExpl) => nExpl.clue != null)[nestedIndex-1]
      const nested_sequence_length = nested_explanations[sequenceIndex-1].reason_sequence.length

      prevNextButton = <div>
          <table>
          <td><button onClick={() => setIndexClipped(index - 1)}>&#8592; Prev</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button className="buttonNavigationCluesExit heavyBorder" onClick={() => setIndexClipped(index)}>Back to MAIN explanations</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button onClick={() => setIndexClipped(index + 1)}>Next &#8594;</button></td>
          </table> 
        </div>  
      
      prevNextSequenceButton = <div>
        <h5 className="blue-font">Nested Explanation</h5>
        <table>
            <td><button onClick={() => setNestedIndexClipped(Math.max(1, nestedIndex-1), nested_sequence_length)}>&#8592;</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button className="buttonNavigationCluesExit heavyBorder" onClick={() => setNestedIndexClipped(0)}>Back to NESTED explanations</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button onClick={() => setNestedIndexClipped(nestedIndex+1, nested_sequence_length)}><span>&#8594;</span></button></td>
        </table> 
        <p />
      </div>
    
    }else if(sequenceIndex > 0){
      
      prevNextButton = <div>
        <table>
        <td><button onClick={() => setIndexClipped(index - 1)}>&#8592; Prev</button></td>
          <td className="buttonNavigationClues"></td>
          <td><button className="buttonNavigationCluesExit heavyBorder" onClick={() => setIndexClipped(index)}>Back to main explanations</button></td>
          <td className="buttonNavigationClues"></td>
          <td><button onClick={() => setIndexClipped(index + 1)}>Next &#8594;</button></td>
        </table> 
      </div>  

    }  
  }else{
        prevNextButton = <div>
          <table>
            <td><button onClick={() => setIndexClipped(index - 1)}>&#8592; Prev</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button className="Disabled" onClick={() => setSequenceIndexClipped(1)}><span role="img"  aria-label="help">&#x1F4A1;</span> - HELP</button></td>
            <td className="buttonNavigationClues"></td>
            <td><button onClick={() => setIndexClipped(index + 1)}>Next &#8594;</button></td>
          </table> 
        </div>
  }

  return (
    <div className="App">
      {header}
      {prevNextButton}
      <p />
      {prevNextSequenceButton}
      <Grid vocabulary={vocabulary} counterfact={counterfact} facts={facts} explSeqActive={sequenceIndex} nestedExplSeqActive={nestedIndex} funSequenceIndex={setSequenceIndexClipped} funNestedIndex={setNestedIndexClipped}/>
    </div>
    );
}


function Grid({ vocabulary, facts, counterfact,explSeqActive,nestedExplSeqActive, funSequenceIndex,funNestedIndex}) {

  const nbTypes = vocabulary.length;
  const nbEntities = vocabulary[0].length;

  const horizontalTypes = vocabulary.slice(0, -1);
  const verticalTypes = [...vocabulary].reverse().slice(0, -1);

  return (
    <div style={styles.parentGrid(nbEntities, nbTypes)}>
      <div style={styles.parentGridItem(nbEntities)} />
      {verticalTypes.map(type => (
        <VocBlock type={type} vertical />
      ))}
      {horizontalTypes.map((type, index) => (
        <>
          <VocBlock type={type} />
          {verticalTypes.map((type2, index2) => {
            if (index >= nbTypes - index2 - 1) {
              return (<div style={styles.parentGridItemEmpty(nbEntities)} />)
            }
            return (
              <FillBlock type1={type} type2={type2} counterfact={counterfact} facts={facts} explSeqActive={explSeqActive} nestedExplSeqActive={nestedExplSeqActive} funSequenceIndex={funSequenceIndex} funNestedIndex={funNestedIndex}/>            
              )
          })}
        </>
      ))}
    </div>
  )
}

function VocBlock({ type, vertical = false }) {
  const nbEntities = type.length;
  return (
    <div style={styles.parentGridItemVoc(nbEntities, vertical)}>
      {type.map((entity) => (
        <div style={styles.childVocGridItem(nbEntities, vertical)}>
          {entity}
        </div>
      ))}
    </div>
  );
}

function EmptyGrid({type1, type2}){
  const nbEntities = type1.length;
  return (
      <div style={styles.parentGridItemFill(nbEntities)}>
        {type1.map(entity1 => (
          <>
            {type2.map(entity2 => {
              const color = "white";
              const frontcolor = "#000";
              return (<div style={styles.childFillGridItem(color, frontcolor)}>{" "}</div>);
            })}
          </>
        ))}
      </div>
  );
}

function RegularExplanation({ type1, type2, facts, counterfact }){
  const nbEntities = type1.length;
  return (
    <div style={styles.parentGridItemFill(nbEntities)}>
      {type1.map(entity1 => (
        <>
          {type2.map(entity2 => {
            const derivedKnowledge = getKnowledgeFrom(
              facts.derived,
              entity1,
              entity2
            );
            const assumedKnowledge = getKnowledgeFrom(
              facts.assumptions,
              entity1,
              entity2
            );
            const knownKnowledge = getKnowledgeFrom(
              facts.known,
              entity1,
              entity2
            );

            let counterfactColored = null

            if(counterfact != null){
              counterfactColored = getKnowledgeFrom(
                [counterfact],
                entity1,
                entity2
              );
            }

            const knowledge = counterfactColored || derivedKnowledge || assumedKnowledge || knownKnowledge ;

            let color = null;
            let frontcolor = "#000";

            if(counterfactColored!=null && facts.derived[0] === "UNSAT"){
              color = "whitesmoke"
            }else if(counterfact != null && facts.derived[0] === "UNSAT" && assumedKnowledge != null){
              color = "red"
            }
            else if(derivedKnowledge != null) {
                color = "#FF6600";
            }else if(assumedKnowledge != null) {
              color = "#003399"; //Asymmetry true/false is not so important here...
              frontcolor = "white";
            }else if (knowledge != null) {
                color = "whitesmoke";
              }
            
            if(counterfactColored!=null){
              return (<div style={styles.childNestedButtonItem(color, frontcolor)}>
                  {knowledge == null ? " " : knowledge.value ? "✔" : "-"}
                </div>);
            }else{
              return (
                <div style={styles.childFillGridItem(color, frontcolor)}>
                  {knowledge == null ? " " : knowledge.value ? "✔" : "-"}
                </div>
              );
            }

          })}
        </>
      ))}
    </div>
  );
}

function SequenceExplanationGrid({ type1, type2, derived, known, funSequenceIndex,funNestedIndex}){
  const nbEntities = type1.length;

  return (
    <div style={styles.parentGridItemFill(nbEntities)}>
      {type1.map(entity1 => (
        <>
          {type2.map(entity2 => {
            const factKnowledge = getKnowledgeFrom(
              derived,
              entity1,
              entity2
            );

            const knownKnowledge = getKnowledgeFrom(
              known, 
              entity1, 
              entity2
            )

            const posInDerived = derived.indexOf(factKnowledge) +1
            
            const knowledge = factKnowledge || knownKnowledge;

            let color = "#C0C0C0";
            let frontcolor = "#000";

            if (factKnowledge != null) {
              color = "lightcoral";// knowledge.value ? "#FF6600" : "#FF6600";
            }else if(knownKnowledge != null){
              color = "whitesmoke";
            }

            if(factKnowledge != null){
              return (
                <div >
                  <button className="coral-button" onClick={() => {funNestedIndex(1, 3); funSequenceIndex(posInDerived)}}>
                    {knowledge == null ? " " : knowledge.value ? "✔" : "-"}
                  </button>        
                </div>
              );
            }else{
              return (
                <div style={styles.childFillGridItem(color, frontcolor)}>
                  {knowledge == null ? " " : knowledge.value ? "✔" : "-"}
                </div>
              );
            }
          })}
        </>
      ))}
    </div>
  );


}

function FillBlock({ type1, type2, counterfact, facts, explSeqActive,nestedExplSeqActive, funSequenceIndex,funNestedIndex }) {

  if(facts === null){
    return <EmptyGrid type1={type1} type2={type2} />
  }else if( explSeqActive > 0 & nestedExplSeqActive > 0){
    return <RegularExplanation facts={facts} counterfact={counterfact} type1={type1} type2={type2}/>
  }else if( explSeqActive > 0){
    return <SequenceExplanationGrid derived={facts.derived} known={facts.assumptions} type1={type1} type2={type2} funSequenceIndex={funSequenceIndex} funNestedIndex={funNestedIndex}/>
  }
  else{
    return <RegularExplanation facts={facts} type1={type1} type2={type2} />
  }
}

function Legend() {
  return (
    <div>
      <h2>
        <span class="line-center">{legend}</span>
      </h2>
      <table>
        <tr className="legend-tr">
          <td className="legend-td2">
            <div className="red-full-rectangle"></div>
          </td>
          <td className="legend-td">{legend_new_fact}</td>
          <td className="legend-td2">
            <div className="blue-full-rectangle"></div>
          </td>
          <td className="legend-td">{legend_derived_fact}</td>
          <td className="legend-td2">
            <div className="coral-full-rectangle"></div>
          </td>
          <td className="legend-td">Nested Explanation</td>          
          <td className="legend-td2">
            <div className="unsat-full-rectangle"></div>
          </td>
          <td className="legend-td">Countradiction Unsatisfiable</td>
              
        </tr>
          <tr className="legend-tr">
          <td className="legend-td2">
            <div className="black-empty-rectangle"> ✔ </div>
          </td>
          <td className="legend-td">{legend_true}</td>
          <td className="legend-td2">
            <div className="black-empty-rectangle"> - </div>
          </td>
          <td className="legend-td">{legend_false}</td>
          <td className="legend-td2">
            <div className="black-solid-empty-rectangle"> - </div>
          </td>
          <td className="legend-td">{legend_contradiction}</td>
        </tr>
      
      </table>
    </div>
  );
}

function UsedClue({ clues, clue }) {
  var unique = 0;
  if(clue !== null){
    const listClues = clues.map((element) => {
      if (
        element === transitivity ||
        element === bijectivity ||
        element === combinationConstraints
      ) {
        if (clue === transitivity && unique === 0) {
          unique = 1;
          return (
            <div>
              <li>{logigramConstraint}</li>
              <ul>
                <li className="clue-used">{transitivity}</li>
                <li className="clue-unused">{bijectivity}</li>
                <li className="clue-unused">{combinationConstraints}</li>
              </ul>
            </div>
          );
        } else if (clue === bijectivity && unique === 0) {
          unique = 1;
          return (
            <div>
              <li>{logigramConstraint}</li>
              <ul>
                <li className="clue-unused">{transitivity}</li>
                <li className="clue-used">{bijectivity}</li>
                <li className="clue-unused">{combinationConstraints}</li>
              </ul>
            </div>
          );
        } else if (clue === combinationConstraints && unique === 0) {
          unique = 1;
          return (
            <div>
              <li>{logigramConstraint}</li>
              <ul>
                <li className="clue-unused">{transitivity}</li>
                <li className="clue-unused">{bijectivity}</li>
                <li className="clue-used">{combinationConstraints}</li>
              </ul>
            </div>
          );
        } else if (unique === 0) {
          unique = 1;
          return (
            <div>
              <li>{logigramConstraint}</li>
              <ul>
                <li className="clue-unused">{transitivity}</li>
                <li className="clue-unused">{bijectivity}</li>
                <li className="clue-unused">{combinationConstraints}</li>
              </ul>
            </div>
          );
        }else{
          return <div></div>
        }
        
      } else if (element === clue) {
        return (
          <li className="clue-used">
            {element.charAt(0).toUpperCase() + element.slice(1)}
          </li>
        );
      } else {
        return (
          <li className="clue-unused">
            {element.charAt(0).toUpperCase() + element.slice(1)}
          </li>
        );
      }
    });
    return <ol>{listClues}</ol>;
  }else{
    const listClues = clues.map((element)=> {
      if (
        element !== transitivity &&
        element !== bijectivity &&
        element !== combinationConstraints
      ){
        return <li className="clue-unused">
            {element.charAt(0).toUpperCase() + element.slice(1)}
          </li>
      }else if(unique === 0){
        unique = 1
        return (
          <div>
            <li>{logigramConstraint}</li>
            <ul>
              <li className="clue-unused">{transitivity}</li>
              <li className="clue-unused">{bijectivity}</li>
              <li className="clue-unused">{combinationConstraints}</li>
            </ul>
          </div>
        );
      }
      return <div></div>
    });
    return <ol>{listClues}</ol>;
  }
  
}

export default App;