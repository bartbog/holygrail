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

let nestedExplanationActive = false;

function switchNestedExplanation(){
  nestedExplanationActive = ~nestedExplanationActive
}

const initialState = {
  clue: null,
  known: [],
  derived: [],
  assumptions: []
};


function reducer(state, next) {
  return {
    clue: next.clue,
    known: [...state.known, ...state.derived],
    derived: next.derivations,
    assumptions: next.assumptions,
    nested_explanations:next.nested_explanations,
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
  steps = require(`../../bos/output/${problemName}.output.json`);
  vocabulary = require(`../../bos/output/${problemName}.voc.json`);

  const clues = cleanClues(steps);

  const [index, setIndex] = React.useState(0);
  const [nestedIndex, setNestedIndex] = React.useState(0)

  const factsOverTime = React.useMemo(() => {
    return cleanedFacts(steps);
  }, []);



 function setIndexClipped(newIndex) {
    nestedExplanationActive = false;
    setNestedIndex(0)
    if (newIndex >= factsOverTime.length) {
      setIndex(factsOverTime.length - 1);
    } else if (newIndex < 0) {
      setIndex(0);
    } else {
      setIndex(newIndex);
    }
  }

  function setNestedIndexClipped(newIndex, maxLength) {

    if (newIndex >= maxLength) {
      setNestedIndex(maxLength);
    } else if (newIndex < 0) {
      setNestedIndex(0);
    } else {
      setNestedIndex(newIndex);
    }
  }

  let facts = null
  let usedClue

  if(index > 0){
    facts = factsOverTime[index-1];
    usedClue = <UsedClue clues={clues} clue={facts.clue} />
  }else{
    usedClue = <UsedClue clues={clues} clue={null} />
  }

   
  ReactDOM.render(
    <div className="Clues">
      <h2>
        <span class="line-center">Clues</span>
      </h2>
      {usedClue}
      <MyLegend />
      <p></p>
    </div>,
    document.getElementById("clues"));

  const header = (
    <h2>
      <span class="line-center">Puzzle</span>
    </h2>
  );
  
  let prevNextButton;

  if( facts === null){
    prevNextButton = 
    <div>
      <button onClick={() => setIndexClipped(index + 1)}>start</button>
    </div>
  } else if(Array.isArray(facts.nested_explanations) && nestedIndex <= 0 ){
    prevNextButton = 
    <div>
      <table>
      <td><button onClick={() => setIndexClipped(index - 1)}>&#8592; Prev</button></td>
        <td className="buttonNavigationClues"></td>
        <td><button onClick={() => setIndexClipped(0)}>Restart</button></td>
        <td className="buttonNavigationClues"></td>
        <td><button onClick={() => setIndexClipped(index + 1)}>Next &#8594;</button></td>
        <td className="buttonNavigationClues"></td>
        <td><button onClick={() => setNestedIndexClipped(1)}>HELP</button></td>
      </table> 
    </div>  
}  else if(Array.isArray(facts.nested_explanations) && nestedIndex > 0 ){
  let maxNestedIndex = facts.nested_reason_sequence
  prevNextButton = 
  <div>
    <table>
    <td><button onClick={() => setNestedIndexClipped(nestedIndex - 1, maxNestedIndex)}>&#8592; Prev Explanation</button></td>
      <td className="buttonNavigationClues"></td>
      <td><button onClick={() => setNestedIndexClipped(0, maxNestedIndex)}>EXIT Explanation</button></td>
      <td className="buttonNavigationClues"></td>
      <td><button onClick={() => setNestedIndexClipped(nestedIndex + 1,maxNestedIndex)}>Next Explanation &#8594;</button></td>
    </table> 
  </div>  
}else{
    prevNextButton = 
    <div>
      <table>
        <td><button onClick={() => setIndexClipped(index - 1)}>&#8592; Prev</button></td>
        <td className="buttonNavigationClues"></td>
        <td><button onClick={() => setIndexClipped(0)}>Restart</button></td>
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
      <Grid vocabulary={vocabulary} facts={facts} nestedFactActive={nestedIndex}/>
    </div>);
       
}

function MyLegend() {
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
            <div className="black-empty-rectangle"> ✔ </div>
          </td>
          <td className="legend-td">{legend_true}</td>
          <td className="legend-td2">
            <div className="black-empty-rectangle"> - </div>
          </td>
          <td className="legend-td">{legend_false}</td>
        </tr>
      </table>
    </div>
  );
}

function UsedClue({ clues, clue }) {
  var unique = 0;
  if(clue !== null){
    const listClues = clues.map(function(element) {
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
    const listClues = clues.map(function(element) {
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
          
    });
    return <ol>{listClues}</ol>;
  }
  
}

function Grid({ vocabulary, facts,nestedFactActive }) {

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
              <FillBlock type1={type} type2={type2} facts={facts} nestedFactActive={nestedFactActive}/>            
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
      {type.map(entity => (
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

function RegularExplanation({ type1, type2, facts }){
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

            const knowledge =
              derivedKnowledge || assumedKnowledge || knownKnowledge;
            let color = null;
            let frontcolor = "#000";
            if (derivedKnowledge != null) {
              color = knowledge.value ? "#FF6600" : "#FF6600";
            } else if (assumedKnowledge != null) {
              color = "#003399"; //Asymmetry true/false is not so important here...
              frontcolor = "white";
            } else if (knowledge != null) {
              color = "whitesmoke";
            }

            return (
              <div style={styles.childFillGridItem(color, frontcolor)}>
                {knowledge == null ? " " : knowledge.value ? "✔" : "-"}
              </div>
            );
          })}
        </>
      ))}
    </div>
  );
}

function NestedExplanationGrid({ type1, type2, facts, nestedFactActive }){
  const nbEntities = type1.length;
  // let sequenceExplanations = facts.nested_explanations.reason_sequence[nestedFactActive-1]

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

            const knowledge = derivedKnowledge || assumedKnowledge;  

            let color = "#C0C0C0";
            let frontcolor = "#000";

            if (derivedKnowledge != null) {
              color = "#FF6600";// knowledge.value ? "#FF6600" : "#FF6600";
            } else if (assumedKnowledge != null) {
              color = "#003399"; //Asymmetry true/false is not so important here...
              frontcolor = "white";
            } else if (knowledge != null) {
              color = "grey";
            }

            return (
              <div style={styles.childFillGridItem(color, frontcolor)}>
                {knowledge == null ? " " : knowledge.value ? "✔" : "-"}
              </div>
            );
          })}
        </>
      ))}
    </div>
  );


}

function FillBlock({ type1, type2, facts, nestedFactActive }) {
  if(facts === null){
    return <EmptyGrid type1={type1} type2={type2} />
  }else if( Array.isArray(facts.nested_explanations) && nestedFactActive > 0){
    // return <RegularExplanation facts={facts} type1={type1} type2={type2} />

    return <NestedExplanationGrid facts={facts} type1={type1} type2={type2} nestedFactActive={nestedFactActive}/>
  }
  else{
    return <RegularExplanation facts={facts} type1={type1} type2={type2} />
  }
}

export default App;
