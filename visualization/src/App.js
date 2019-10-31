import React from 'react';
import './App.css';
import * as R from 'ramda'
import ReactDOM from 'react-dom';

const problemName = 'p5'
const steps = require(`../../bos/output/${problemName}.output.json`)
const vocabulary = require(`../../bos/output/${problemName}.voc.json`)

const sol = "Solution!"
const logicon = "Logigram constraints"

const initialState = {
  clue: null,
  known: [],
  derived: [],
  assumptions: []
}
function reducer(state, next) {
  return {
    clue: next.clue,
    known: [...state.known, ...state.derived],
    derived: next.derivations,
    assumptions: next.assumptions,
  }
}
function cleanedFacts(steps) {
  const factsOverTime = R.scan(reducer, initialState, steps)
  return factsOverTime.filter(
    facts => facts.derived.some(
      knowledge => getKnowledgeFrom(facts.known, knowledge.subject, knowledge.object) == null
    )
  )
}

function getKnowledgeFrom(inArray, entity1, entity2) {
  return inArray.find(matches(entity1, entity2))
}

function matches(entity1, entity2) {
  return fact => {
    if (fact.subject === entity1 && fact.object === entity2) {
      return true
    }
    if (fact.object === entity1 && fact.subject === entity2) {
      return true
    }
    return false
  }
}

const size = 35
const styles = {
  parentGrid: (nbEntities, nbTypes) => ({
    display: 'grid',
    width: nbEntities * nbTypes * size,
    height: nbEntities * nbTypes * size,
    "grid-template-columns": `auto `.repeat(nbTypes),
  }),
  parentGridItem: (nbEntities) => ({
    width: size * nbEntities - 2,
    height: size * nbEntities - 2,
    border: '1px solid black',
  }),
  parentGridItemVoc: (nbEntities, vertical) => ({
    ...styles.parentGridItem(nbEntities),
    'background-color': 'whitesmoke',
    color: 'black',
    display: 'grid',
    "grid-template-columns": `auto `.repeat(vertical ? nbEntities : 1),
    'flex-direction': vertical ? 'row' : 'column',
  }),
  childVocGridItem: (nbEntities, vertical) => ({
    border: '1px dashed black',
    display: 'flex',
    'align-items': 'center',
    'justify-content': 'center',
    ...(vertical ? {
      'writing-mode': 'vertical-lr',
      width: size - 2,
      height: size * nbEntities - 2,
    } : {
        width: size * nbEntities - 2,
        height: size - 2,
      })
  }),
  parentGridItemEmpty: (nbEntities) => ({
    width: nbEntities * size,
    height: nbEntities * size,
  }),
  parentGridItemFill: (nbEntities) => ({
    ...styles.parentGridItem(nbEntities),
    display: 'grid',
    "grid-template-columns": `auto `.repeat(nbEntities),
  }),
  childFillGridItem: (color, frontcolor) => ({
    width: size - 2,
    height: size - 2,
    border: '1px dashed black',
    display: 'flex',
    'align-items': 'center',
    'justify-content': 'center',
    'background-color': color,
    'color': frontcolor,
  })
}

function cleanClues(steps){
  const clues = steps.map(element => element.clue);
  const uniqueclues = clues.filter(function(item, pos) {
    return clues.indexOf(item) === pos;
  })

  for(var i = uniqueclues.length - 1; i >= 0; i--) {
    if(uniqueclues[i] === logicon || uniqueclues[i] === sol) {
      uniqueclues.splice(i, 1);
    }
}
uniqueclues.push(logicon)
  return uniqueclues
}

function App() {
  const clues = cleanClues(steps)

  const [index, setIndex] = React.useState(0)
  const factsOverTime = React.useMemo(() => {
    return cleanedFacts(steps)
  }, [])

  function setIndexClipped(newIndex) {
    if (newIndex >= factsOverTime.length) {
      setIndex(factsOverTime.length - 1)
    } else if (newIndex < 0) {
      setIndex(0)
    } else {
      setIndex(newIndex)
    }
  }
  const facts = factsOverTime[index]

  ReactDOM.render(
    <div className="Clues">
      <h2>Clues</h2>
      <UsedClue clues={clues} clue={facts.clue}/>
      <p></p>
      <MyLegend />
      <p></p>
    </div>,
    document.getElementById('clues')
  );
  


  return (
    <div className="App">
      <h2>Puzzle</h2>
      <div>
        <button onClick={() => setIndexClipped(index - 1)}>Prev</button>
        <button onClick={() => setIndexClipped(index + 1)}>Next</button>
      </div>
      <p />
      <Grid vocabulary={vocabulary} facts={facts} />
    </div>
  );
}

function MyLegend(){
  return (
  <div>
    <h2>Legend</h2>
    <table>
  <tr>
    <td><div className="red-full-rectangle"></div></td>
    <td>&nbsp;&nbsp;&nbsp;New fact</td>
  </tr>
  <tr>
    <td></td>
    <td></td>
  </tr>
  <tr>
  <td><div className="blue-full-rectangle"></div></td>
    <td>&nbsp;&nbsp;&nbsp;Derived fact</td>
  </tr>
  <tr>
    <td></td>
    <td></td>
  </tr>
  <tr>
  <td><div className="black-empty-rectangle"> ✔</div></td>
    <td>&nbsp;&nbsp;&nbsp;True</td>
  </tr>
  <tr>
    <td></td>
    <td></td>
  </tr>
  <tr>
  <td><div className="black-empty-rectangle"> - </div></td>
    <td>&nbsp;&nbsp;&nbsp;False</td>
  </tr>
</table> 
  </div>)
}


function UsedClue({ clues, clue }) {

  const listClues = clues.map(function(element) {
      if(element === logicon){
        if(clue === logicon){
          return (<div>
                    <li  className="clue-used">
                      {logicon}
                      </li>
                    <ul>
                      <li>Transitity</li>
                      <li>Bijection</li>
                      <li>Inverse relation</li>
                    </ul> 
                  </div>)
        }else{
          return (<div>
                    <li className="clue-unused">{logicon}</li>
                    <ul>
                      <li>Transitity</li>
                      <li>Bijection</li>
                      <li>Inverse relation</li>
                    </ul> 
                  </div>)
        }
        
      } else if(element === clue){
        return <li className="clue-used">{element}</li>
      }else{
        return <li className="clue-unused">{element}</li>
      }
    }
  );
  return (<ol>{listClues}</ol>)
}

function Grid({ vocabulary, facts }) {
  const nbTypes = vocabulary.length
  const nbEntities = vocabulary[0].length

  const horizontalTypes = vocabulary.slice(0, -1)
  const verticalTypes = [...vocabulary].reverse().slice(0, -1)

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
              <FillBlock type1={type} type2={type2} facts={facts} />
            )
          })}
        </>
      ))}
    </div>
  )
}

function VocBlock({ type, vertical = false }) {
  const nbEntities = type.length
  return (
    <div style={styles.parentGridItemVoc(nbEntities, vertical)}>
      {type.map(entity => (
        <div style={styles.childVocGridItem(nbEntities, vertical)}>{entity}</div>
      ))}
    </div>
  )
}

function FillBlock({ type1, type2, facts }) {
  const nbEntities = type1.length
  return (
    <div style={styles.parentGridItemFill(nbEntities)}>
      {type1.map(entity1 => (
        <>
          {type2.map(entity2 => {
            const derivedKnowledge = getKnowledgeFrom(facts.derived, entity1, entity2)
            const assumedKnowledge = getKnowledgeFrom(facts.assumptions, entity1, entity2)
            const knownKnowledge = getKnowledgeFrom(facts.known, entity1, entity2)

            const knowledge = derivedKnowledge || assumedKnowledge || knownKnowledge
            let color = null
            let frontcolor = '#000'
            if (derivedKnowledge != null) {
              color = knowledge.value ? '#FF6600' : '#FF6600'
            } else if (assumedKnowledge != null) {
              color = '#003399' //Asymmetry true/false is not so important here... 
              frontcolor = 'white'
            } else if (knowledge != null) {
              color = 'whitesmoke'
            }

            return (
              <div style={styles.childFillGridItem(color, frontcolor)}>{knowledge == null ? ' ' : knowledge.value ? '✔' : '-'}</div>
            )
          })}
        </>
      )
      )}
    </div>
  )
}
export default App;
