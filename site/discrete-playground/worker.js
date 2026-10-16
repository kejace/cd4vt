import createSolver from './solver.mjs';
// Buffer layout of solver.c: stride N = 25; κ, previous κ, previous lengths in;
// lengths, vertices, then ten metrics out.
const N=25, METRICS=3*N;
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
    kernel.HEAPF64.fill(0,input,input+3*N);
    kernel.HEAPF64.set(k,input);
    if (previous) {
      kernel.HEAPF64.set(previous.k,input+N);
      kernel.HEAPF64.set(previous.lengths,input+2*N);
    }
    const start=performance.now();
    const status=kernel._solve(n,mode,seed);
    const milliseconds=performance.now()-start;
    const values=kernel.HEAPF64.slice(output,output+METRICS+10);
    postMessage({type:'result', id, k, status, milliseconds,
      lengths:Array.from(values.slice(0,n)),
      vertices:Array.from({length:n},(_,i)=>[values[N+2*i],values[N+1+2*i]]),
      metrics:{closure:values[METRICS],turn:values[METRICS+1],curvature:values[METRICS+2],wall:values[METRICS+3],minLength:values[METRICS+4],evaluations:values[METRICS+5],attempts:values[METRICS+6],method:values[METRICS+7],activeMask:values[METRICS+8],support:values[METRICS+9]}});
  } catch (error) {
    postMessage({type:'result',id,k,status:0,message:String(error)});
  }
};
