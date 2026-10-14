import createSolver from './solver.mjs';
let kernel;
try {
  kernel = await createSolver();
  postMessage({type:'ready'});
} catch (error) {
  postMessage({type:'fatal', message:String(error)});
}
onmessage = ({data}) => {
  if (!kernel || data.type !== 'solve') return;
  const {id, k, previous, seed, mode} = data;
  try {
    const n=k.length, input=kernel._input_buffer()/8, output=kernel._output_buffer()/8;
    kernel.HEAPF64.fill(0,input,input+36);
    kernel.HEAPF64.set(k,input);
    if (previous) {
      kernel.HEAPF64.set(previous.k,input+12);
      kernel.HEAPF64.set(previous.lengths,input+24);
    }
    const start=performance.now();
    const status=kernel._solve(n,mode,seed);
    const milliseconds=performance.now()-start;
    const values=kernel.HEAPF64.slice(output,output+64);
    postMessage({type:'result', id, k, status, milliseconds,
      lengths:Array.from(values.slice(0,n)),
      vertices:Array.from({length:n},(_,i)=>[values[12+2*i],values[13+2*i]]),
      metrics:{closure:values[36],turn:values[37],curvature:values[38],wall:values[39],minLength:values[40],evaluations:values[41],attempts:values[42],method:values[43],activeMask:values[44],support:values[45]}});
  } catch (error) {
    postMessage({type:'result',id,k,status:0,message:String(error)});
  }
};
