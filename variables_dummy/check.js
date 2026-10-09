
"use strict";
const $ = s => document.querySelector(s);
const CS = () => getComputedStyle(document.documentElement);
const col = v => CS().getPropertyValue(v).trim();

/* ══════════ Utilidades numéricas ══════════ */
function matInv(A){
  const n = A.length;
  const M = A.map((r,i) => [...r, ...Array.from({length:n}, (_,j) => i===j?1:0)]);
  for(let c=0;c<n;c++){
    let p=c;
    for(let r=c+1;r<n;r++) if(Math.abs(M[r][c])>Math.abs(M[p][c])) p=r;
    if(Math.abs(M[p][c])<1e-12) return null;
    const tmp=M[c]; M[c]=M[p]; M[p]=tmp;
    const pv=M[c][c];
    for(let j=0;j<2*n;j++) M[c][j]/=pv;
    for(let r=0;r<n;r++){
      if(r===c) continue;
      const f=M[r][c];
      if(f===0) continue;
      for(let j=0;j<2*n;j++) M[r][j]-=f*M[c][j];
    }
  }
  return M.map(r=>r.slice(n));
}

function ols(X,y){
  const n=X.length, k=X[0].length;
  const XtX=Array.from({length:k},()=>Array(k).fill(0));
  const Xty=Array(k).fill(0);
  for(let i=0;i<n;i++){
    for(let a=0;a<k;a++){
      Xty[a]+=X[i][a]*y[i];
      for(let b=0;b<k;b++) XtX[a][b]+=X[i][a]*X[i][b];
    }
  }
  const inv=matInv(XtX);
  if(!inv) return null;
  const b=Array(k).fill(0);
  for(let a=0;a<k;a++) for(let j=0;j<k;j++) b[a]+=inv[a][j]*Xty[j];
  const yhat=X.map(r=>r.reduce((s,v,j)=>s+v*b[j],0));
  const res=y.map((v,i)=>v-yhat[i]);
  const SSR=res.reduce((s,v)=>s+v*v,0);
  const ybar=y.reduce((s,v)=>s+v,0)/n;
  const SST=y.reduce((s,v)=>s+(v-ybar)**2,0);
  const df=n-k;
  const sigma2=df>0?SSR/df:NaN;
  const se=b.map((_,i)=>Math.sqrt(sigma2*inv[i][i]));
  return {b, se, inv, n, k, df, SSR, SST, sigma2, sigma:Math.sqrt(sigma2),
          R2: SST>0 ? 1-SSR/SST : NaN, yhat, res, ybar};
}

function quadForm(inv, v){
  let s=0;
  for(let a=0;a<v.length;a++) for(let b=0;b<v.length;b++) s+=v[a]*inv[a][b]*v[b];
  return s;
}

function normInv(p){
  const a=[-3.969683028665376e+01,2.209460984245205e+02,-2.759285104469687e+02,1.383577518672690e+02,-3.066479806614716e+01,2.506628277459239e+00];
  const b=[-5.447609879822406e+01,1.615858368580409e+02,-1.556989798598866e+02,6.680131188771972e+01,-1.328068155288572e+01];
  const c=[-7.784894002430293e-03,-3.223964580411365e-01,-2.400758277161838e+00,-2.549732539343734e+00,4.374664141464968e+00,2.938163982698783e+00];
  const d=[7.784695709041462e-03,3.224671290700398e-01,2.445134137142996e+00,3.754408661907416e+00];
  const pl=0.02425;
  let q,r;
  if(p<pl){
    q=Math.sqrt(-2*Math.log(p));
    return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])/((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1);
  }
  if(p<=1-pl){
    q=p-0.5; r=q*q;
    return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q/(((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1);
  }
  q=Math.sqrt(-2*Math.log(1-p));
  return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])/((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1);
}

/* Cuantil t por expansión de Cornish-Fisher (buena para df >= 8) */
function tInv(p, df){
  const z=normInv(p);
  if(!isFinite(df) || df>2000) return z;
  const z2=z*z, z3=z2*z, z5=z3*z2, z7=z5*z2, z9=z7*z2;
  const g1=(z3+z)/4;
  const g2=(5*z5+16*z3+3*z)/96;
  const g3=(3*z7+19*z5+17*z3-15*z)/384;
  const g4=(79*z9+776*z7+1482*z5-1920*z3-945*z)/92160;
  return z + g1/df + g2/(df*df) + g3/(df**3) + g4/(df**4);
}

function mulberry32(a){
  return function(){
    a|=0; a=a+0x6D2B79F5|0;
    let t=Math.imul(a^a>>>15, 1|a);
    t=t+Math.imul(t^t>>>7, 61|t)^t;
    return ((t^t>>>14)>>>0)/4294967296;
  };
}
function normGen(rng){
  let spare=null;
  return ()=>{
    if(spare!==null){const v=spare; spare=null; return v;}
    let u=0,v=0;
    while(u===0) u=rng();
    while(v===0) v=rng();
    const m=Math.sqrt(-2*Math.log(u));
    spare=m*Math.sin(2*Math.PI*v);
    return m*Math.cos(2*Math.PI*v);
  };
}

const mean = a => a.reduce((s,v)=>s+v,0)/a.length;
const fmt = (v,d=3) => (isFinite(v)? v.toFixed(d) : '—');
function fmtSmart(v){
  if(!isFinite(v)) return '—';
  const a=Math.abs(v);
  if(a===0) return '0';
  if(a<0.001) return Number(v.toFixed(7)).toString();
  if(a<1) return v.toFixed(4);
  if(a<100) return v.toFixed(3);
  return v.toFixed(1);
}
function statCards(items){
  return items.map(s=>`<div class="stat-card"><div class="stat-label">${s.l}</div><div class="stat-value ${s.c||''} ${s.sm?'sm':''}">${s.v}</div>${s.note?`<div class="stat-note">${s.note}</div>`:''}</div>`).join('');
}

/* ══════════ Canvas helpers ══════════ */
function setupCanvas(id, ratio, maxH){
  const canvas=document.getElementById(id);
  const dpr=window.devicePixelRatio||1;
  const cw=canvas.parentElement.clientWidth||760;
  // En pantallas angostas la altura proporcional queda demasiado chata para
  // leer los gráficos, así que imponemos un piso más alto.
  const ch=Math.min(maxH||420, Math.max(cw<520?240:190, cw*ratio));
  canvas.width=Math.round(cw*dpr);
  canvas.height=Math.round(ch*dpr);
  canvas.style.width=cw+'px';
  canvas.style.height=ch+'px';
  const ctx=canvas.getContext('2d');
  ctx.setTransform(dpr,0,0,dpr,0,0);
  return {canvas, ctx, cw, ch};
}

/* Formatea las marcas de un eje con la cantidad de decimales que hace falta
   para distinguir dos marcas consecutivas, y no más. */
function tickFmt(lo, hi, n){
  const step=(hi-lo)/n;
  if(!isFinite(step) || step<=0) return v=>String(v);
  const d=Math.min(6, Math.max(0, Math.ceil(-Math.log10(step))+1));
  return v=>{
    const s=(Math.abs(v)<step/1e6 ? 0 : v).toFixed(d);
    return s==='-0'?'0':s;
  };
}

function frame(ctx, cw, ch, pad, xr, yr, opts){
  opts=opts||{};
  const pw=cw-pad.l-pad.r, ph=ch-pad.t-pad.b;
  const [x0,x1]=xr, [y0,y1]=yr;
  const sx=v=>pad.l+(v-x0)/(x1-x0)*pw;
  const sy=v=>pad.t+ph-(v-y0)/(y1-y0)*ph;
  const ix=px=>x0+(px-pad.l)/pw*(x1-x0);

  ctx.fillStyle=col('--bg-canvas');
  ctx.fillRect(0,0,cw,ch);

  const nx=opts.nx||6, ny=opts.ny||5;
  const fx=opts.fx||tickFmt(x0,x1,nx);
  const fy=opts.fy||tickFmt(y0,y1,ny);
  ctx.strokeStyle=col('--border');
  ctx.lineWidth=0.5;
  ctx.font='11px sans-serif';
  for(let i=0;i<=nx;i++){
    const v=x0+(x1-x0)*i/nx, px=sx(v);
    ctx.beginPath(); ctx.moveTo(px,pad.t); ctx.lineTo(px,pad.t+ph); ctx.stroke();
    ctx.fillStyle=col('--text-sec'); ctx.textAlign='center';
    ctx.fillText(fx(v), px, pad.t+ph+16);
  }
  for(let i=0;i<=ny;i++){
    const v=y0+(y1-y0)*i/ny, py=sy(v);
    ctx.beginPath(); ctx.moveTo(pad.l,py); ctx.lineTo(pad.l+pw,py); ctx.stroke();
    ctx.fillStyle=col('--text-sec'); ctx.textAlign='right';
    ctx.fillText(fy(v), pad.l-8, py+4);
  }
  ctx.strokeStyle=col('--text-sec'); ctx.lineWidth=1;
  ctx.beginPath(); ctx.moveTo(pad.l,pad.t+ph); ctx.lineTo(pad.l+pw,pad.t+ph); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(pad.l,pad.t); ctx.lineTo(pad.l,pad.t+ph); ctx.stroke();

  ctx.fillStyle=col('--heading'); ctx.font='bold 12px sans-serif'; ctx.textAlign='center';
  if(opts.xlab) ctx.fillText(opts.xlab, pad.l+pw/2, ch-4);
  if(opts.ylab){
    ctx.save(); ctx.translate(13, pad.t+ph/2); ctx.rotate(-Math.PI/2);
    ctx.fillText(opts.ylab, 0, 0); ctx.restore();
  }
  return {sx, sy, ix, pw, ph, x0, x1, y0, y1};
}

function nicePad(lo, hi, frac){
  frac=frac||0.08;
  if(!isFinite(lo)||!isFinite(hi)) return [0,1];
  if(hi-lo<1e-9){ const d=Math.abs(hi)*0.1||1; return [lo-d, hi+d]; }
  const p=(hi-lo)*frac;
  return [lo-p, hi+p];
}

function polyline(ctx, sc, f, x0, x1, steps){
  ctx.beginPath();
  let started=false;
  for(let i=0;i<=steps;i++){
    const x=x0+(x1-x0)*i/steps;
    const y=f(x);
    if(!isFinite(y)) { started=false; continue; }
    const px=sc.sx(x), py=sc.sy(y);
    if(!started){ ctx.moveTo(px,py); started=true; } else ctx.lineTo(px,py);
  }
  ctx.stroke();
}

/* ══════════ Distribución F (para p-valores del test de Chow) ══════════ */
function lgamma(x){
  const g=[76.18009172947146,-86.50532032941677,24.01409824083091,
           -1.231739572450155,0.1208650973866179e-2,-0.5395239384953e-5];
  let xx=x, y=x, tmp=xx+5.5;
  tmp-=(xx+0.5)*Math.log(tmp);
  let ser=1.000000000190015;
  for(let j=0;j<6;j++) ser+=g[j]/++y;
  return -tmp+Math.log(2.5066282746310005*ser/xx);
}
function betacf(a,b,x){
  const MAXIT=200, EPS=3e-12, FPMIN=1e-300;
  const qab=a+b, qap=a+1, qam=a-1;
  let c=1, d=1-qab*x/qap;
  if(Math.abs(d)<FPMIN) d=FPMIN;
  d=1/d;
  let h=d;
  for(let m=1;m<=MAXIT;m++){
    const m2=2*m;
    let aa=m*(b-m)*x/((qam+m2)*(a+m2));
    d=1+aa*d; if(Math.abs(d)<FPMIN) d=FPMIN;
    c=1+aa/c; if(Math.abs(c)<FPMIN) c=FPMIN;
    d=1/d; h*=d*c;
    aa=-(a+m)*(qab+m)*x/((a+m2)*(qap+m2));
    d=1+aa*d; if(Math.abs(d)<FPMIN) d=FPMIN;
    c=1+aa/c; if(Math.abs(c)<FPMIN) c=FPMIN;
    d=1/d;
    const del=d*c; h*=del;
    if(Math.abs(del-1)<EPS) break;
  }
  return h;
}
function betai(a,b,x){
  if(x<=0) return 0;
  if(x>=1) return 1;
  const bt=Math.exp(lgamma(a+b)-lgamma(a)-lgamma(b)+a*Math.log(x)+b*Math.log(1-x));
  return x < (a+1)/(a+b+2) ? bt*betacf(a,b,x)/a : 1-bt*betacf(b,a,1-x)/b;
}
/* P(F_{d1,d2} > f) */
function fTail(f,d1,d2){
  if(!isFinite(f) || f<=0) return 1;
  return betai(d2/2, d1/2, d2/(d2+d1*f));
}
/* Valor crítico de F por bisección */
function fCrit(alpha,d1,d2){
  let lo=0.001, hi=1000;
  for(let i=0;i<200;i++){
    const mid=(lo+hi)/2;
    if(fTail(mid,d1,d2)>alpha) lo=mid; else hi=mid;
  }
  return (lo+hi)/2;
}
/* P(|t_df| > |t|) */
function tTail2(t,df){
  const x=df/(df+t*t);
  return betai(df/2, 0.5, x);
}

/* ══════════ Helper de dibujo: nube de puntos por grupo ══════════ */
function scatterGroups(ctx, sc, x, y, D, colors, r){
  r=r||2.6;
  for(let i=0;i<x.length;i++){
    ctx.fillStyle=col(colors[D[i]]);
    ctx.globalAlpha=0.5;
    ctx.beginPath(); ctx.arc(sc.sx(x[i]), sc.sy(y[i]), r, 0, 2*Math.PI); ctx.fill();
  }
  ctx.globalAlpha=1;
}
function drawLine(ctx, sc, f, x0, x1, color, width, dash){
  ctx.save();
  ctx.strokeStyle=col(color); ctx.lineWidth=width||2.4;
  if(dash) ctx.setLineDash(dash);
  polyline(ctx, sc, f, x0, x1, 60);
  ctx.restore();
}
function coefTable(names, b, se, df, extra){
  let h='<thead><tr><th>Variable</th><th>β̂</th><th>se</th><th>t</th><th>p-valor</th><th></th></tr></thead><tbody>';
  names.forEach((nm,i)=>{
    const t=b[i]/se[i], p=tTail2(t,df);
    const sig = p<0.01?'***':(p<0.05?'**':(p<0.10?'*':''));
    h+=`<tr><td class="lbl">${nm}</td><td>${fmt(b[i],4)}</td><td>${fmt(se[i],4)}</td>`
     + `<td>${fmt(t,2)}</td><td>${p<0.0005?'&lt;0.001':fmt(p,3)}</td><td>${sig}</td></tr>`;
  });
  if(extra) h+=extra;
  return h+'</tbody>';
}

/* ══════════════════════════════════════════════════════
   LAB 1 — Codificador de dummies
   ══════════════════════════════════════════════════════ */
const PERSONAS=[
  {n:'Ana',      g:'M', r:'Sur'},
  {n:'Bruno',    g:'V', r:'Norte'},
  {n:'Carla',    g:'M', r:'Centro'},
  {n:'Diego',    g:'V', r:'Sur'},
  {n:'Elena',    g:'M', r:'Norte'},
  {n:'Franco',   g:'V', r:'Centro'},
  {n:'Gabriela', g:'M', r:'Norte'},
  {n:'Hugo',     g:'V', r:'Sur'}
];
const REGIONES=['Sur','Centro','Norte'];

function renderCoder(){
  const genOne=$('#cdGen').value;             // 'M' o 'V'
  const base=$('#cdBase').value;
  const all=$('#cdAll').value==='1';
  const genName = genOne==='M' ? 'mujer' : 'varon';
  const genBase = genOne==='M' ? 'varones' : 'mujeres';
  const regCols = all ? REGIONES.slice() : REGIONES.filter(r=>r!==base);

  let h='<thead><tr><th>Persona</th><th>Género</th><th>Región</th><th>constante</th>'
      + `<th>${genName}</th>`;
  regCols.forEach(r=>{ h+=`<th${(all&&r===base)?' class="base"':''}>${r.toLowerCase()}</th>`; });
  if(all) h+='<th class="drop">suma de las 3</th>';
  h+='</tr></thead><tbody>';

  PERSONAS.forEach(p=>{
    const gv = (p.g===genOne)?1:0;
    h+=`<tr><td class="lbl">${p.n}</td><td>${p.g==='M'?'Mujer':'Varón'}</td><td>${p.r}</td>`
     + '<td class="dummy1">1</td>'
     + `<td class="${gv?'dummy1':'dummy0'}">${gv}</td>`;
    regCols.forEach(r=>{
      const v=(p.r===r)?1:0;
      h+=`<td class="${v?'dummy1':'dummy0'}">${v}</td>`;
    });
    if(all) h+='<td class="drop">1</td>';
    h+='</tr>';
  });
  h+='</tbody>';
  $('#cdTable').innerHTML=h;

  // Verificación numérica: ¿se puede invertir X'X?
  const X=PERSONAS.map(p=>{
    const row=[1, (p.g===genOne)?1:0];
    regCols.forEach(r=>row.push(p.r===r?1:0));
    return row;
  });
  const k=X[0].length;
  const XtX=Array.from({length:k},()=>Array(k).fill(0));
  for(const row of X) for(let a=0;a<k;a++) for(let b=0;b<k;b++) XtX[a][b]+=row[a]*row[b];
  const inv=matInv(XtX);

  const notes=[];
  if(all){
    notes.push(`<div class="callout" style="margin-top:1rem"><div class="callout-title">Colinealidad perfecta: el modelo no se puede estimar</div>
      La última columna muestra que <span class="math">sur + centro + norte = 1</span> en todas las observaciones: las tres dummies suman exactamente la columna de la constante. Al intentar invertir <span class="math">X&prime;X</span> el algoritmo devuelve
      <strong>${inv===null?'una matriz singular':'un resultado inestable'}</strong>: no hay una única combinación de coeficientes que ajuste los datos, hay infinitas.
      En R o Stata no vas a ver un error: el software <em>silenciosamente descarta</em> una de las dummies y elige una base por vos. Conviene elegirla uno mismo.</div>`);
  } else {
    notes.push(`<div class="tip" style="margin-top:1rem"><strong>Qué representa cada columna.</strong>
      La constante recoge al individuo con <em>todas</em> las dummies en cero: en esta configuración, alguien del grupo <strong>${genBase}</strong> y de la región <strong>${base}</strong>. Ese es el <strong>grupo base del modelo</strong>, y todas las diferencias se miden respecto de él.
      Con 2 categorías de género va 1 dummy y con 3 de región van 2: en total ${1+regCols.length} dummies más la constante, y <span class="math">X&prime;X</span> es invertible.</div>`);
  }
  $('#cdNotes').innerHTML=notes.join('');
}

/* ══════════════════════════════════════════════════════
   LAB 2 — Ordenada, pendiente y ambas
   ══════════════════════════════════════════════════════ */
const DU_B0=2, DU_B1=0.55;
let duSeed=20250908, duSpec=2;
function newDumSample(){ duSeed=Math.floor(Math.random()*1e9); runDum(); }
function setDumSpec(s){
  duSpec=s;
  document.querySelectorAll('#dumSpecs .btn').forEach(b=>b.classList.toggle('active', +b.dataset.spec===s));
  runDum();
}
function genGroupData(seed, n, d0, d1, sig, b0, b1){
  const rng=mulberry32(seed), rn=normGen(rng);
  const x=[], y=[], D=[];
  for(let i=0;i<n;i++){
    const Di=i%2;
    const xi=6+14*rng();
    const yi=(b0+d0*Di)+(b1+d1*Di)*xi+sig*rn();
    D.push(Di); x.push(xi); y.push(yi);
  }
  return {x,y,D};
}
function designFor(spec, x, D){
  return x.map((xi,i)=>{
    if(spec===1) return [1, xi];
    if(spec===2) return [1, D[i], xi];
    if(spec===3) return [1, xi, D[i]*xi];
    return [1, D[i], xi, D[i]*xi];
  });
}
function namesFor(spec){
  if(spec===1) return ['Constante','educ'];
  if(spec===2) return ['Constante','mujer (δ₀)','educ'];
  if(spec===3) return ['Constante','educ','mujer×educ (δ₁)'];
  return ['Constante','mujer (δ₀)','educ','mujer×educ (δ₁)'];
}
function lineFor(spec, b, D){
  // Devuelve [ordenada, pendiente] del grupo D bajo la especificación spec
  if(spec===1) return [b[0], b[1]];
  if(spec===2) return [b[0]+D*b[1], b[2]];
  if(spec===3) return [b[0], b[1]+D*b[2]];
  return [b[0]+D*b[1], b[2]+D*b[3]];
}

let duState=null;
function runDum(){
  const d0=parseFloat($('#duD0').value), d1=parseFloat($('#duD1').value);
  const n=parseInt($('#duN').value), sig=parseFloat($('#duSig').value);
  $('#duD0Val').textContent=d0.toFixed(2);
  $('#duD1Val').textContent=d1.toFixed(2);
  $('#duNVal').textContent=n;
  $('#duSigVal').textContent=sig.toFixed(2);

  const dat=genGroupData(duSeed, n, d0, d1, sig, DU_B0, DU_B1);
  const X=designFor(duSpec, dat.x, dat.D);
  const r=ols(X, dat.y);
  duState={dat, r, d0, d1};
  if(!r) return;

  const nm=namesFor(duSpec);
  const extra=`<tr><td class="lbl">R²</td><td colspan="5">${fmt(r.R2,4)} &nbsp;·&nbsp; SCR = ${fmt(r.SSR,2)} &nbsp;·&nbsp; n = ${r.n}</td></tr>`;
  $('#duTable').innerHTML=coefTable(nm, r.b, r.se, r.df, extra);

  const L0=lineFor(duSpec, r.b, 0), L1=lineFor(duSpec, r.b, 1);
  $('#duEqs').innerHTML=
    `<div class="eq-line"><span class="tag g0">Varones</span> salario&#770; = ${fmt(L0[0],3)} + ${fmt(L0[1],3)}·educ</div>
     <div class="eq-line"><span class="tag g1">Mujeres</span> salario&#770; = ${fmt(L1[0],3)} + ${fmt(L1[1],3)}·educ</div>`;

  drawDum();

  const brecha12 = (L1[0]+L1[1]*12) - (L0[0]+L0[1]*12);
  const dpend = L1[1]-L0[1];
  const cruce = Math.abs(dpend)>1e-9 ? -(L1[0]-L0[0])/dpend : NaN;
  const cruceTxt = !isFinite(cruce) ? 'no se cruzan' :
                   (cruce>=4 && cruce<=24 ? 'educ ≈ '+fmt(cruce,1) : 'fuera del gráfico');
  $('#duStats').innerHTML=statCards([
    {l:'Pendiente varones', v:fmt(L0[1],3), c:'accent'},
    {l:'Pendiente mujeres', v:fmt(L1[1],3), c:'orange'},
    {l:'Brecha en educ = 12', v:fmt(brecha12,3), c: brecha12<0?'orange':'green', note:'diferencia mujeres − varones'},
    {l:'Punto de cruce', v:cruceTxt, c:'purple', sm:true},
    {l:'SCR', v:fmt(r.SSR,1), note:'suma de cuadrados de los residuos'}
  ]);

  const notes=[];
  if(duSpec===1 && (Math.abs(d0)>0.3 || Math.abs(d1)>0.03)){
    notes.push('<div class="callout" style="margin-top:1rem"><div class="callout-title">Modelo mal especificado</div>Los grupos difieren de verdad, pero el modelo estimado no tiene forma de expresarlo: ajusta <strong>una sola recta</strong> que pasa por el medio de las dos nubes. Los residuos quedan sistemáticamente positivos para un grupo y negativos para el otro, algo que se ve a simple vista en el gráfico. Es un caso de <strong>variable omitida</strong>: la dummy está en el error.</div>');
  }
  if(duSpec===2 && Math.abs(d1)>0.08){
    notes.push('<div class="note" style="margin-top:1rem"><div class="note-title">Las rectas son paralelas por imposición, no por los datos</div>El modelo de rectas paralelas obliga a que las dos pendientes sean iguales, pero en la población no lo son. El resultado es una pendiente única de compromiso y una brecha estimada que no describe bien a ningún nivel de educación. Pasá a <strong>disímiles</strong> y compará el SCR.</div>');
  }
  if(duSpec===3 && Math.abs(d0)>0.8){
    notes.push('<div class="note" style="margin-top:1rem"><div class="note-title">Rectas concurrentes: obligadas a arrancar del mismo punto</div>Sin la dummy sola, las dos rectas comparten ordenada en educ = 0 y solo pueden separarse abriéndose en abanico. Es una especificación poco frecuente en la práctica: si se permite que la pendiente difiera, casi siempre hay que permitir también que difiera la ordenada.</div>');
  }
  if(duSpec===4){
    const t3=r.b[3]/r.se[3], p3=tTail2(t3,r.df);
    notes.push(`<div class="tip" style="margin-top:1rem"><strong>¿Las pendientes difieren?</strong> El test es H₀: δ₁ = 0 sobre el coeficiente de la interacción: t = ${fmt(t3,2)}, p = ${fmt(p3,3)}. ${p3<0.05?'Se <strong>rechaza</strong> al 5%: hay evidencia de que el rendimiento de la educación difiere entre grupos.':'<strong>No</strong> se rechaza al 5%: los datos no permiten afirmar que el rendimiento de la educación difiera entre grupos. Ojo con la lectura: no significativo no es lo mismo que igual a cero, sobre todo con n chico o mucho ruido.'}</div>`);
  }
  $('#duNotes').innerHTML=notes.join('');
}

function drawDum(){
  if(!duState) return;
  const {dat, r, d0, d1}=duState;
  const c=setupCanvas('duCanvas', 0.5, 430);
  const pad={t:16,r:20,b:44,l:58};
  const yr=nicePad(Math.min(...dat.y), Math.max(...dat.y), 0.08);
  const sc=frame(c.ctx, c.cw, c.ch, pad, [5,21], yr, {xlab:'Educación (años)', ylab:'Salario por hora'});
  const ctx=c.ctx;
  scatterGroups(ctx, sc, dat.x, dat.y, dat.D, ['--accent','--red']);
  // Rectas verdaderas
  drawLine(ctx, sc, x=>DU_B0+DU_B1*x, 5, 21, '--text-sec', 1.3, [4,4]);
  drawLine(ctx, sc, x=>(DU_B0+d0)+(DU_B1+d1)*x, 5, 21, '--text-sec', 1.3, [4,4]);
  // Rectas estimadas
  const L0=lineFor(duSpec, r.b, 0), L1=lineFor(duSpec, r.b, 1);
  drawLine(ctx, sc, x=>L0[0]+L0[1]*x, 5, 21, '--accent', 2.8);
  drawLine(ctx, sc, x=>L1[0]+L1[1]*x, 5, 21, '--red', 2.8);
  ctx.fillStyle=col('--text-sec'); ctx.font='11px sans-serif'; ctx.textAlign='right';
  ctx.fillText('punteado = verdad poblacional', c.cw-pad.r, pad.t+12);
}

/* ══════════════════════════════════════════════════════
   LAB 3 — Dar vuelta la dummy
   ══════════════════════════════════════════════════════ */
let flSeed=777001, flState=null;
function newFlipSample(){ flSeed=Math.floor(Math.random()*1e9); runFlip(); }

function runFlip(){
  const spec=parseInt($('#flSpec').value);
  const d0=parseFloat($('#flD0').value), d1=parseFloat($('#flD1').value);
  $('#flD0Val').textContent=d0.toFixed(2);
  $('#flD1Val').textContent=d1.toFixed(2);
  $('#flD1').parentElement.style.opacity = spec===4 ? '1' : '.4';

  const dat=genGroupData(flSeed, 300, d0, spec===4?d1:0, 1.5, DU_B0, DU_B1);
  const M=dat.D;                      // mujer = 1
  const V=dat.D.map(v=>1-v);          // varon = 1

  const XA=designFor(spec, dat.x, M);
  const XB=designFor(spec, dat.x, V);
  const rA=ols(XA, dat.y), rB=ols(XB, dat.y);
  flState={dat, rA, spec};
  if(!rA||!rB) return;

  const nmA = spec===2 ? ['Constante','mujer','educ'] : ['Constante','mujer','educ','mujer×educ'];
  const nmB = spec===2 ? ['Constante','varon','educ'] : ['Constante','varon','educ','varon×educ'];
  const exA=`<tr><td class="lbl">R²</td><td colspan="5">${fmt(rA.R2,5)}</td></tr>`
           +`<tr><td class="lbl">SCR</td><td colspan="5">${fmt(rA.SSR,3)}</td></tr>`;
  const exB=`<tr><td class="lbl">R²</td><td colspan="5">${fmt(rB.R2,5)}</td></tr>`
           +`<tr><td class="lbl">SCR</td><td colspan="5">${fmt(rB.SSR,3)}</td></tr>`;
  $('#flTableA').innerHTML=coefTable(nmA, rA.b, rA.se, rA.df, exA);
  $('#flTableB').innerHTML=coefTable(nmB, rB.b, rB.se, rB.df, exB);

  drawFlip();

  const same=(a,b)=>Math.abs(a-b)<1e-8;
  const pills=[
    {t:'R² idéntico', ok:same(rA.R2,rB.R2)},
    {t:'SCR idéntico', ok:same(rA.SSR,rB.SSR)},
    {t:'σ̂ idéntico', ok:same(rA.sigma,rB.sigma)},
    {t:'|t| de la dummy idéntico', ok:same(Math.abs(rA.b[1]/rA.se[1]), Math.abs(rB.b[1]/rB.se[1]))},
    {t:'Predicciones idénticas', ok:true},
    {t:'Constante distinta', ok:false},
    {t:'Signo de la dummy invertido', ok:false}
  ];
  if(spec===4) pills.push({t:'Pendiente de educ distinta', ok:false});
  $('#flPills').innerHTML=pills.map(p=>`<span class="inv-pill ${p.ok?'':'chg'}">${p.ok?'no cambia':'cambia'} · ${p.t}</span>`).join('');

  const notes=[];
  notes.push(`<div class="tip" style="margin-top:1rem"><strong>Las identidades algebraicas, verificadas en estos datos.</strong>
    La constante de B es la constante de A más el coeficiente de la dummy: ${fmt(rA.b[0],4)} + (${fmt(rA.b[1],4)}) = <strong>${fmt(rA.b[0]+rA.b[1],4)}</strong>, y efectivamente la constante de B vale ${fmt(rB.b[0],4)}.
    El coeficiente de la dummy cambia de signo: ${fmt(rA.b[1],4)} → ${fmt(rB.b[1],4)}. Y su error estándar es el mismo (${fmt(rA.se[1],4)}), así que el <span class="math">t</span> solo cambia de signo y la conclusión del test es idéntica.</div>`);
  if(spec===4){
    notes.push(`<div class="callout" style="margin-top:1rem"><div class="callout-title">Con interacción, "educ" ya no significa lo mismo en las dos versiones</div>
      El coeficiente de <span class="math">educ</span> es siempre <strong>la pendiente del grupo base</strong>. En la versión A (base varones) vale ${fmt(rA.b[2],4)}, la pendiente de los varones. En la versión B (base mujeres) vale ${fmt(rB.b[2],4)}, la pendiente de las mujeres. No es que el modelo cambió: cambió qué grupo quedó de referencia. Y se cumple ${fmt(rA.b[2],4)} + (${fmt(rA.b[3],4)}) = ${fmt(rA.b[2]+rA.b[3],4)}.
      Este es el error de lectura más frecuente en modelos con interacciones.</div>`);
  }
  $('#flNotes').innerHTML=notes.join('');
}

function drawFlip(){
  if(!flState) return;
  const {dat, rA, spec}=flState;
  const c=setupCanvas('flCanvas', 0.42, 340);
  const pad={t:16,r:20,b:44,l:58};
  const yr=nicePad(Math.min(...dat.y), Math.max(...dat.y), 0.08);
  const sc=frame(c.ctx, c.cw, c.ch, pad, [5,21], yr, {xlab:'Educación (años)', ylab:'Salario por hora'});
  const ctx=c.ctx;
  scatterGroups(ctx, sc, dat.x, dat.y, dat.D, ['--accent','--red'], 2.2);
  const L0=lineFor(spec, rA.b, 0), L1=lineFor(spec, rA.b, 1);
  drawLine(ctx, sc, x=>L0[0]+L0[1]*x, 5, 21, '--accent', 2.8);
  drawLine(ctx, sc, x=>L1[0]+L1[1]*x, 5, 21, '--red', 2.8);
}

/* ══════════════════════════════════════════════════════
   LAB 4 — Cambiar la categoría base (regiones)
   ══════════════════════════════════════════════════════ */
/* Parametrización original del Ejercicio 3, base = Sur */
const RG={ b_educ:4.20, b_exper:1.15, const_:22.00, d:{Sur:0, Centro:8.50, Norte:15.30},
           se:{Centro:3.40, Norte:4.10, const_:5.60}, n:350, R2:0.412 };
const RGCOL={Sur:'--accent', Centro:'--green', Norte:'--red'};

function renderRegion(){
  const base=$('#rgBase').value;
  const educ=parseInt($('#rgEduc').value), exper=parseInt($('#rgExper').value);
  $('#rgEducVal').textContent=educ;
  $('#rgExperVal').textContent=exper;

  const others=REGIONES.filter(r=>r!==base);
  const cte=RG.const_+RG.d[base];
  const coef={}; others.forEach(r=>{ coef[r]=RG.d[r]-RG.d[base]; });

  let h='<thead><tr><th>Variable</th><th>β̂ con base Sur (original)</th>'
      + `<th>β̂ con base ${base}</th><th>Interpretación</th></tr></thead><tbody>`;
  h+=`<tr><td class="lbl">educ</td><td>${fmt(RG.b_educ,2)}</td><td>${fmt(RG.b_educ,2)}</td>`
   + '<td class="txt">Un año más de educación: +4.20 mil $, en cualquier región. No se mueve nunca.</td></tr>';
  h+=`<tr><td class="lbl">exper</td><td>${fmt(RG.b_exper,2)}</td><td>${fmt(RG.b_exper,2)}</td>`
   + '<td class="txt">Un año más de experiencia: +1.15 mil $. Tampoco se mueve.</td></tr>';
  REGIONES.forEach(r=>{
    if(r===base){
      h+=`<tr class="hi"><td class="lbl">${r}</td><td>${r==='Sur'?'— (base)':fmt(RG.d[r],2)}</td>`
       + '<td>— (base)</td><td class="txt">Es la categoría omitida: su efecto queda absorbido por la constante.</td></tr>';
    } else {
      h+=`<tr><td class="lbl">${r}</td><td>${r==='Sur'?'— (base)':fmt(RG.d[r],2)}</td>`
       + `<td><strong>${coef[r]>0?'+':''}${fmt(coef[r],2)}</strong></td>`
       + `<td class="txt">Un trabajador de ${r} gana ${fmt(Math.abs(coef[r]),2)} mil $ ${coef[r]>=0?'más':'menos'} que uno de ${base}, a igual educación y experiencia.</td></tr>`;
    }
  });
  h+=`<tr><td class="lbl">Constante</td><td>${fmt(RG.const_,2)}</td><td><strong>${fmt(cte,2)}</strong></td>`
   + `<td class="txt">Salario predicho de un trabajador de ${base} con educ = 0 y exper = 0.</td></tr>`;
  h+=`<tr><td class="lbl">R²</td><td>${RG.R2}</td><td>${RG.R2}</td><td class="txt">Idéntico: es el mismo modelo, reescrito.</td></tr>`;
  h+='</tbody>';
  $('#rgTable').innerHTML=h;

  const pred={}; REGIONES.forEach(r=>{ pred[r]=RG.const_+RG.d[r]+RG.b_educ*educ+RG.b_exper*exper; });
  const maxp=Math.max(...REGIONES.map(r=>pred[r]));
  $('#rgBars').innerHTML=REGIONES.map(r=>
    `<div class="bar-row"><span class="bar-name">${r}${r===base?' (base)':''}</span>
      <span class="bar-track"><span class="bar-fill" style="width:${100*pred[r]/maxp}%;background:var(${RGCOL[r]})"></span></span>
      <span class="bar-val">${fmt(pred[r],1)}</span></div>`).join('');

  drawRegion();

  const dNC=RG.d.Norte-RG.d.Centro;
  const notes=[];
  notes.push(`<div class="tip" style="margin-top:1rem"><strong>Ecuaciones estimadas con base ${base}</strong><br>
    ${REGIONES.map(r=>`<span class="math">${r}:</span> salario&#770; = ${fmt(cte,2)}${r===base?'':` ${coef[r]>=0?'+':'−'} ${fmt(Math.abs(coef[r]),2)}`} + 4.20·educ + 1.15·exper`).join('<br>')}
    <br><br>Con educ = ${educ} y exper = ${exper} las tres predicciones son ${REGIONES.map(r=>`${r}: <strong>${fmt(pred[r],2)}</strong>`).join(', ')} mil $ — <strong>las mismas con cualquier base</strong>.</div>`);
  if(base==='Centro'){
    notes.push(`<div class="note" style="margin-top:1rem"><div class="note-title">Justo lo que pedía el Ejercicio 3.c</div>Con Centro como base, el coeficiente de Norte pasa a ser directamente la brecha Norte–Centro: <strong>${fmt(dNC,2)}</strong> mil $. Ahora la salida de regresión reporta su error estándar y su <span class="math">t</span>, y el test es inmediato. Con base Sur ese mismo número había que calcularlo a mano como 15.30 − 8.50, sin forma directa de testearlo.</div>`);
  }
  $('#rgNotes').innerHTML=notes.join('');
}

let rgLast=null;
function drawRegion(){
  const exper=parseInt($('#rgExper').value);
  rgLast=exper;
  const c=setupCanvas('rgCanvas', 0.42, 340);
  const pad={t:16,r:20,b:44,l:62};
  const ys=REGIONES.map(r=>RG.const_+RG.d[r]+RG.b_educ*20+RG.b_exper*exper);
  const y0=RG.const_+RG.b_exper*exper;
  const sc=frame(c.ctx, c.cw, c.ch, pad, [0,20], nicePad(y0*0.9, Math.max(...ys), 0.06),
                 {xlab:'Educación (años)', ylab:'Salario predicho (miles $)'});
  const ctx=c.ctx;
  REGIONES.forEach(r=>{
    drawLine(ctx, sc, x=>RG.const_+RG.d[r]+RG.b_educ*x+RG.b_exper*exper, 0, 20, RGCOL[r], 2.6);
  });
  const educ=parseInt($('#rgEduc').value);
  ctx.strokeStyle=col('--text-sec'); ctx.lineWidth=1; ctx.setLineDash([3,3]);
  ctx.beginPath(); ctx.moveTo(sc.sx(educ), pad.t); ctx.lineTo(sc.sx(educ), c.ch-pad.b); ctx.stroke();
  ctx.setLineDash([]);
  REGIONES.forEach(r=>{
    const yv=RG.const_+RG.d[r]+RG.b_educ*educ+RG.b_exper*exper;
    ctx.fillStyle=col(RGCOL[r]);
    ctx.beginPath(); ctx.arc(sc.sx(educ), sc.sy(yv), 4.5, 0, 2*Math.PI); ctx.fill();
  });
}

/* ══════════════════════════════════════════════════════
   LAB 5 — Dummies vs. codificar 1, 2, 3
   ══════════════════════════════════════════════════════ */
function renderLinCode(){
  const m=[parseFloat($('#lcSur').value), parseFloat($('#lcCen').value), parseFloat($('#lcNor').value)];
  $('#lcSurVal').textContent=m[0].toFixed(1);
  $('#lcCenVal').textContent=m[1].toFixed(1);
  $('#lcNorVal').textContent=m[2].toFixed(1);

  // Ajuste por mínimos cuadrados de una recta sobre los códigos 1, 2, 3
  const codes=[1,2,3];
  const cbar=2, mbar=(m[0]+m[1]+m[2])/3;
  let sxy=0, sxx=0;
  for(let i=0;i<3;i++){ sxy+=(codes[i]-cbar)*(m[i]-mbar); sxx+=(codes[i]-cbar)**2; }
  const slope=sxy/sxx, inter=mbar-slope*cbar;
  const fitLin=c=>inter+slope*c;
  const err=[0,1,2].map(i=>m[i]-fitLin(codes[i]));
  const ssrLin=err.reduce((s,v)=>s+v*v,0);

  const salto1=m[1]-m[0], salto2=m[2]-m[1];

  const c=setupCanvas('lcCanvas', 0.38, 310);
  const pad={t:18,r:20,b:44,l:60};
  const lo=Math.min(...m, ...codes.map(fitLin)), hi=Math.max(...m, ...codes.map(fitLin));
  const sc=frame(c.ctx, c.cw, c.ch, pad, [0.6,3.4], nicePad(lo,hi,0.15),
                 {xlab:'Región (Sur = 1, Centro = 2, Norte = 3)', ylab:'Salario medio', nx:4, fx:v=>{
                   const r=Math.round(v);
                   return Math.abs(v-r)<0.01 && r>=1 && r<=3 ? ['','Sur','Centro','Norte'][r] : '';
                 }});
  const ctx=c.ctx;
  // Recta forzada por la codificación numérica
  drawLine(ctx, sc, fitLin, 0.8, 3.2, '--red', 2.6);
  // Ajuste con dummies: pasa por las tres medias
  ctx.strokeStyle=col('--accent'); ctx.lineWidth=2.6;
  ctx.beginPath();
  for(let i=0;i<3;i++){ const px=sc.sx(codes[i]), py=sc.sy(m[i]); i===0?ctx.moveTo(px,py):ctx.lineTo(px,py); }
  ctx.stroke();
  for(let i=0;i<3;i++){
    ctx.fillStyle=col('--accent');
    ctx.beginPath(); ctx.arc(sc.sx(codes[i]), sc.sy(m[i]), 5.5, 0, 2*Math.PI); ctx.fill();
    ctx.strokeStyle=col('--bg-canvas'); ctx.lineWidth=2; ctx.stroke();
    // Residuo de la codificación numérica
    if(Math.abs(err[i])>0.05){
      ctx.strokeStyle=col('--red'); ctx.lineWidth=1.2; ctx.setLineDash([2,2]);
      ctx.beginPath(); ctx.moveTo(sc.sx(codes[i]), sc.sy(m[i])); ctx.lineTo(sc.sx(codes[i]), sc.sy(fitLin(codes[i]))); ctx.stroke();
      ctx.setLineDash([]);
    }
  }

  $('#lcStats').innerHTML=statCards([
    {l:'Salto Sur → Centro', v:fmt(salto1,2), c:'accent'},
    {l:'Salto Centro → Norte', v:fmt(salto2,2), c:'accent'},
    {l:'Salto único impuesto por 1,2,3', v:fmt(slope,2), c:'orange', note:'δ̂ de la variable codificada'},
    {l:'Error del ajuste forzado', v:fmt(ssrLin,3), c: ssrLin>0.01?'orange':'green', note:'0 solo si los dos saltos son iguales'}
  ]);

  const dif=Math.abs(salto1-salto2);
  const notes=[];
  if(dif<0.2){
    notes.push('<div class="tip" style="margin-top:1rem"><strong>Este es el único caso en que la codificación 1, 2, 3 no hace daño.</strong> Los dos saltos son prácticamente iguales, así que la recta forzada pasa por las tres medias y ahorra un parámetro. El problema es que <em>eso no se sabe de antemano</em>: uno lo descubre después de estimar con dummies. Y si además la variable no tiene un orden natural (industria, provincia, estado civil), asignar números es directamente indefendible.</div>');
  } else {
    notes.push(`<div class="callout" style="margin-top:1rem"><div class="callout-title">La restricción se ve a simple vista</div>
      Los saltos verdaderos son ${fmt(salto1,2)} y ${fmt(salto2,2)}, pero la codificación numérica solo puede ofrecer <strong>un único salto de ${fmt(slope,2)}</strong> repetido dos veces. Las líneas punteadas rojas son lo que el modelo no puede capturar. Con dummies no hay nada que forzar: dos coeficientes describen exactamente dos saltos (Ejercicio 3.d).</div>`);
  }
  notes.push('<div class="note" style="margin-top:1rem"><div class="note-title">Y el orden también es arbitrario</div>Si en lugar de Sur = 1, Centro = 2, Norte = 3 hubiéramos puesto Centro = 1, Norte = 2, Sur = 3, la recta ajustada sería otra y el coeficiente estimado también. Con dummies el resultado no depende de en qué orden escribas las categorías.</div>');
  $('#lcNotes').innerHTML=notes.join('');
}

/* ══════════════════════════════════════════════════════
   LAB 6 — Interacción entre dos dummies
   ══════════════════════════════════════════════════════ */
function presetInter(){
  $('#inB0').value=0.321; $('#inD1').value=-0.110; $('#inD2').value=0.213;
  $('#inD3').value=-0.301; $('#inSe').value=0.072;
  renderInter();
}
function renderInter(){
  const b0=parseFloat($('#inB0').value), d1=parseFloat($('#inD1').value);
  const d2=parseFloat($('#inD2').value), d3=parseFloat($('#inD3').value);
  const se3=parseFloat($('#inSe').value);
  $('#inB0Val').textContent=b0.toFixed(3);
  $('#inD1Val').textContent=d1.toFixed(3);
  $('#inD2Val').textContent=d2.toFixed(3);
  $('#inD3Val').textContent=d3.toFixed(3);
  $('#inSeVal').textContent=se3.toFixed(3);

  const cells=[
    {n:'Varón soltero',  v:b0,          f:'β₀'},
    {n:'Varón casado',   v:b0+d2,       f:'β₀ + δ₂'},
    {n:'Mujer soltera',  v:b0+d1,       f:'β₀ + δ₁'},
    {n:'Mujer casada',   v:b0+d1+d2+d3, f:'β₀ + δ₁ + δ₂ + δ₃'}
  ];

  $('#inCells').innerHTML=
    `<div class="hd"></div><div class="hd">Soltero/a (casado = 0)</div><div class="hd">Casado/a (casado = 1)</div>
     <div class="hd">Varón<br>(mujer = 0)</div>
     <div><span class="cform">${cells[0].f}</span><span class="cval">${fmt(cells[0].v,3)}</span></div>
     <div><span class="cform">${cells[1].f}</span><span class="cval">${fmt(cells[1].v,3)}</span></div>
     <div class="hd">Mujer<br>(mujer = 1)</div>
     <div><span class="cform">${cells[2].f}</span><span class="cval">${fmt(cells[2].v,3)}</span></div>
     <div><span class="cform">${cells[3].f}</span><span class="cval">${fmt(cells[3].v,3)}</span></div>`;

  const vals=cells.map(c=>c.v);
  const lo=Math.min(...vals), hi=Math.max(...vals);
  const span=(hi-lo)||1;
  const colors=['--accent','--green','--orange','--red'];
  $('#inBars').innerHTML='<h3>ln(wage) predicho por grupo</h3>'+cells.map((c,i)=>
    `<div class="bar-row"><span class="bar-name">${c.n}</span>
      <span class="bar-track"><span class="bar-fill" style="width:${8+92*(c.v-lo+span*0.08)/(span*1.16)}%;background:var(${colors[i]})"></span></span>
      <span class="bar-val">${fmt(c.v,3)}</span></div>`).join('');

  const primaV=d2, primaM=d2+d3;
  const t3=d3/se3, p3=tTail2(t3, 500);
  const maxG=cells.reduce((a,b)=>b.v>a.v?b:a), minG=cells.reduce((a,b)=>b.v<a.v?b:a);
  $('#inStats').innerHTML=statCards([
    {l:'Prima de casado · varones', v:(primaV>=0?'+':'')+fmt(100*primaV,1)+'%', c:primaV>=0?'green':'orange', note:'δ₂ · 100 (aprox.)'},
    {l:'Prima de casado · mujeres', v:(primaM>=0?'+':'')+fmt(100*primaM,1)+'%', c:primaM>=0?'green':'orange', note:'(δ₂ + δ₃) · 100 (aprox.)'},
    {l:'Diferencia entre primas', v:fmt(100*d3,1)+' p.p.', c:'purple', note:'es exactamente δ₃'},
    {l:'t de la interacción', v:fmt(t3,2), c: Math.abs(t3)>1.96?'green':'orange', note:'p = '+(p3<0.001?'<0.001':fmt(p3,3))},
    {l:'Mayor ln(wage) predicho', v:maxG.n, sm:true},
    {l:'Menor ln(wage) predicho', v:minG.n, sm:true}
  ]);
  renderInterEquiv(b0,d1,d2,d3,cells,t3,primaV,primaM);
}

function renderInterEquiv(b0,d1,d2,d3,cells,t3,primaV,primaM){
  let h='<thead><tr><th>Parametrización</th><th>Coeficientes</th><th>Interceptos que produce</th></tr></thead><tbody>';
  h+='<tr><td class="lbl">Con interacción</td>'
   + `<td class="txt">β₀ = ${fmt(b0,3)}, mujer = ${fmt(d1,3)}, casado = ${fmt(d2,3)}, mujer×casado = ${fmt(d3,3)}</td>`
   + `<td class="txt">${cells.map(c=>`${c.n}: ${fmt(c.v,3)}`).join(' · ')}</td></tr>`;
  h+='<tr><td class="lbl">Tres dummies de grupo</td>'
   + `<td class="txt">β₀ = ${fmt(b0,3)}, vcasado = ${fmt(d2,3)}, msoltera = ${fmt(d1,3)}, mcasada = ${fmt(d1+d2+d3,3)}</td>`
   + `<td class="txt">${cells.map(c=>`${c.n}: ${fmt(c.v,3)}`).join(' · ')}</td></tr>`;
  h+='<tr><td class="lbl">R², SCR, predicciones</td><td colspan="2" class="txt">Idénticos. Son el mismo modelo escrito de dos maneras: cuatro parámetros para describir cuatro celdas.</td></tr>';
  h+='</tbody>';
  $('#inEquiv').innerHTML=h;

  const notes=[];
  if(Math.abs(t3)>1.96){
    notes.push(`<div class="tip" style="margin-top:1rem"><strong>La interacción es significativa</strong> (|t| = ${fmt(Math.abs(t3),2)} &gt; 1.96): hay evidencia de que el efecto del estado civil <em>difiere</em> según el género. Casarse se asocia con salarios ${primaV>0?'más altos':'más bajos'} para los varones (${fmt(100*primaV,1)}%) y ${primaM>0?'más altos':'más bajos'} para las mujeres (${fmt(100*primaM,1)}%). Un modelo sin interacción no podría representar este patrón: estaría obligado a asignar la misma prima a los dos grupos.</div>`);
  } else {
    notes.push(`<div class="note" style="margin-top:1rem"><div class="note-title">La interacción no es significativa</div>Con |t| = ${fmt(Math.abs(t3),2)} no se rechaza H₀: δ₃ = 0 al 5%. Los datos son compatibles con una prima de casado igual para ambos géneros. Eso <em>no prueba</em> que sean iguales: puede ser falta de precisión. Antes de sacar la interacción del modelo conviene mirar el intervalo de confianza de δ₃ y ver si excluye efectos económicamente importantes.</div>`);
  }
  notes.push('<div class="note" style="margin-top:1rem"><div class="note-title">Nunca dejar la interacción sin sus términos principales</div>Estimar <span class="math">mujer×casado</span> sin incluir <span class="math">mujer</span> y <span class="math">casado</span> por separado impone, sin ninguna justificación, que tres de las cuatro celdas compartan el mismo intercepto. Salvo que la teoría lo exija, la interacción va siempre acompañada de sus componentes.</div>');
  $('#inNotes').innerHTML=notes.join('');
}

/* ══════════════════════════════════════════════════════
   LAB 7 — ln(y): aproximado, exacto y asimetría de la base
   ══════════════════════════════════════════════════════ */
function renderLog(){
  const d=parseFloat($('#lgD').value);
  $('#lgDVal').textContent=d.toFixed(3);
  const apx=100*d;
  const exacto=100*(Math.exp(d)-1);
  const inverso=100*(Math.exp(-d)-1);
  const errorRel=Math.abs(apx-exacto);

  $('#lgStats').innerHTML=statCards([
    {l:'Aproximación 100·δ̂', v:(apx>=0?'+':'')+fmt(apx,1)+'%', c:'accent'},
    {l:'Exacto 100·(e^δ̂ − 1)', v:(exacto>=0?'+':'')+fmt(exacto,1)+'%', c:'orange', note:'grupo D=1 respecto del grupo base'},
    {l:'Exacto dando vuelta la base', v:(inverso>=0?'+':'')+fmt(inverso,1)+'%', c:'green', note:'grupo base respecto del grupo D=1'},
    {l:'Error de la aproximación', v:fmt(errorRel,2)+' p.p.', c: errorRel>2?'orange':'', note: Math.abs(d)<0.1?'despreciable':'ya no es despreciable'},
    {l:'Razón de salarios e^δ̂', v:fmt(Math.exp(d),3)+'×', c:'purple', note:'cuántas veces gana el grupo D=1'}
  ]);

  const vals=[Math.abs(apx), Math.abs(exacto), Math.abs(inverso)];
  const mx=Math.max(...vals)||1;
  $('#lgBars').innerHTML=
    `<div class="bar-row"><span class="bar-name">Aproximado</span><span class="bar-track"><span class="bar-fill" style="width:${100*vals[0]/mx}%;background:var(--accent)"></span></span><span class="bar-val">${fmt(apx,1)}%</span></div>
     <div class="bar-row"><span class="bar-name">Exacto (base original)</span><span class="bar-track"><span class="bar-fill" style="width:${100*vals[1]/mx}%;background:var(--red)"></span></span><span class="bar-val">${fmt(exacto,1)}%</span></div>
     <div class="bar-row"><span class="bar-name">Exacto (base al revés)</span><span class="bar-track"><span class="bar-fill" style="width:${100*vals[2]/mx}%;background:var(--green)"></span></span><span class="bar-val">${fmt(inverso,1)}%</span></div>`;

  drawLogCanvas(d, apx, exacto, inverso);

  const entre = Math.abs(apx) >= Math.min(Math.abs(exacto), Math.abs(inverso)) - 1e-9
             && Math.abs(apx) <= Math.max(Math.abs(exacto), Math.abs(inverso)) + 1e-9;
  let txt;
  if(Math.abs(d)<0.10){
    txt=`<div class="tip" style="margin-top:1rem"><strong>Zona segura.</strong> Con |δ̂| = ${fmt(Math.abs(d),3)} menor que 0.10 las tres curvas están casi pegadas: aproximar cuesta apenas ${fmt(errorRel,2)} puntos porcentuales. Acá la lectura 100·δ̂ es perfectamente aceptable.</div>`;
  } else {
    txt=`<div class="callout" style="margin-top:1rem"><div class="callout-title">Acá ya conviene el cálculo exacto</div>
      Con δ̂ = ${fmt(d,3)} la aproximación dice ${fmt(apx,1)}% y el valor exacto es ${fmt(exacto,1)}%: ${fmt(errorRel,2)} puntos porcentuales de diferencia. Y mirá la asimetría: la misma brecha se reporta como ${fmt(exacto,1)}% o como ${fmt(inverso,1)}% según qué grupo pongas de referencia.
      ${entre?'Notá que 100·|δ̂| = '+fmt(Math.abs(apx),1)+'% queda justo entre los dos valores exactos.':''}</div>`;
  }
  $('#lgNotes').innerHTML=txt;
}

function drawLogCanvas(d, apx, exacto, inverso){
  const c=setupCanvas('lgCanvas', 0.36, 300);
  const pad={t:16,r:20,b:44,l:66};
  const sc=frame(c.ctx, c.cw, c.ch, pad, [-1,1], [-100,180],
                 {xlab:'δ̂ (coeficiente de la dummy)', ylab:'Diferencia porcentual', fy:v=>v.toFixed(0)+'%'});
  const ctx=c.ctx;
  ctx.strokeStyle=col('--border'); ctx.lineWidth=1;
  ctx.beginPath(); ctx.moveTo(sc.sx(-1), sc.sy(0)); ctx.lineTo(sc.sx(1), sc.sy(0)); ctx.stroke();
  drawLine(ctx, sc, v=>100*v, -1, 1, '--accent', 2.4);
  drawLine(ctx, sc, v=>100*(Math.exp(v)-1), -1, 1, '--red', 2.4);
  drawLine(ctx, sc, v=>100*(Math.exp(-v)-1), -1, 1, '--green', 2, [5,4]);
  [[apx,'--accent'],[exacto,'--red'],[inverso,'--green']].forEach(function(pair){
    const v=pair[0], cc=pair[1];
    if(v>=-100 && v<=180){
      ctx.fillStyle=col(cc);
      ctx.beginPath(); ctx.arc(sc.sx(d), sc.sy(v), 4.5, 0, 2*Math.PI); ctx.fill();
      ctx.strokeStyle=col('--bg-canvas'); ctx.lineWidth=1.8; ctx.stroke();
    }
  });
}

/* ══════════════════════════════════════════════════════
   LAB 8 — Test de Chow
   ══════════════════════════════════════════════════════ */
let chSeed=424242, chState=null;
function newChowSample(){ chSeed=Math.floor(Math.random()*1e9); runChow(); }

function runChow(){
  const d0=parseFloat($('#chD0').value), d1=parseFloat($('#chD1').value);
  const n=parseInt($('#chN').value), sig=parseFloat($('#chSig').value);
  $('#chD0Val').textContent=d0.toFixed(2);
  $('#chD1Val').textContent=d1.toFixed(3);
  $('#chNVal').textContent=n;
  $('#chSigVal').textContent=sig.toFixed(2);

  const dat=genGroupData(chSeed, n, d0, d1, sig, DU_B0, DU_B1);
  const k=2;                                   // constante + educ en cada regresión
  const Xp=dat.x.map(v=>[1,v]);
  const rP=ols(Xp, dat.y);
  const idx0=[], idx1=[];
  dat.D.forEach((v,i)=>(v===0?idx0:idx1).push(i));
  const r0=ols(idx0.map(i=>[1,dat.x[i]]), idx0.map(i=>dat.y[i]));
  const r1=ols(idx1.map(i=>[1,dat.x[i]]), idx1.map(i=>dat.y[i]));
  if(!rP||!r0||!r1) return;

  const scrR=rP.SSR, scrNR=r0.SSR+r1.SSR;
  const df1=k, df2=n-2*k;
  const F=((scrR-scrNR)/df1)/(scrNR/df2);
  const p=fTail(F,df1,df2);
  const fc=fCrit(0.05,df1,df2);
  chState={dat, rP, r0, r1};

  $('#chStats').innerHTML=statCards([
    {l:'SCR conjunta (restringida)', v:fmt(scrR,2), c:'purple'},
    {l:'SCR grupo 0 + grupo 1', v:fmt(scrNR,2), c:'accent', note:fmt(r0.SSR,2)+' + '+fmt(r1.SSR,2)},
    {l:'Ganancia de ajuste', v:fmt(scrR-scrNR,2), c:'green', note:'siempre ≥ 0'},
    {l:'F de Chow', v:fmt(F,2), c: p<0.05?'green':'orange', note:`F(${df1}, ${df2})`},
    {l:'Valor crítico al 5%', v:fmt(fc,2), sm:true},
    {l:'p-valor', v: p<0.0001?'<0.0001':fmt(p,4), c: p<0.05?'green':'orange'}
  ]);

  drawChow();

  const rechaza = p<0.05;
  const h0Cierta = Math.abs(d0)<1e-9 && Math.abs(d1)<1e-9;
  let v;
  if(rechaza && h0Cierta){
    v=`<div class="callout" style="margin-top:1rem"><div class="callout-title">Rechazaste, pero H₀ era verdadera: error de tipo I</div>
      Acá vos sabés que los dos grupos tienen exactamente los mismos parámetros poblacionales, y aun así F = ${fmt(F,2)} supera el crítico ${fmt(fc,2)}. Es el 5% de las muestras en que esto pasa por azar. Apretá <strong>Nueva muestra</strong> varias veces: vas a ver que rechaza aproximadamente 1 de cada 20 veces. Eso <em>es</em> el nivel de significatividad.</div>`;
  } else if(rechaza){
    v=`<div class="tip" style="margin-top:1rem"><strong>Se rechaza H₀ al 5%</strong> (F = ${fmt(F,2)} &gt; ${fmt(fc,2)}, p = ${p<0.0001?'<0.0001':fmt(p,4)}). Hay evidencia de que la función de regresión difiere entre grupos. Pero el test no dice <em>qué</em> difiere: para eso hay que mirar la descomposición de abajo.</div>`;
  } else if(!h0Cierta){
    v=`<div class="note" style="margin-top:1rem"><div class="note-title">No se rechaza, aunque los grupos sí difieren</div>
      Las diferencias verdaderas no son cero, pero el test no las detecta (F = ${fmt(F,2)} &lt; ${fmt(fc,2)}). Es un <strong>error de tipo II</strong>: falta potencia. Subí n, bajá σ o agrandá las diferencias y mirá cómo el F despega.</div>`;
  } else {
    v=`<div class="tip" style="margin-top:1rem"><strong>No se rechaza H₀</strong> (F = ${fmt(F,2)} &lt; ${fmt(fc,2)}), y en efecto los dos grupos son idénticos en la población. El test acertó. Fijate que estimar dos rectas igual reduce el SCR (de ${fmt(scrR,2)} a ${fmt(scrNR,2)}): siempre lo hace, aunque no haya nada que capturar. Por eso el F pondera esa ganancia contra los grados de libertad que costó.</div>`;
  }
  $('#chVerdict').innerHTML=v;
  renderChowDecomp(dat, n, scrR, scrNR, df2);
}

function renderChowDecomp(dat, n, scrR, scrNR, df2){
  // Modelo con dummy sola (rectas paralelas): permite que difiera solo el intercepto
  const rPar=ols(designFor(2, dat.x, dat.D), dat.y);
  if(!rPar) return;
  const scrPar=rPar.SSR;
  // F del intercepto: conjunta vs. paralelas (1 restricción, gl del modelo NR completo)
  const Fint=((scrR-scrPar)/1)/(scrNR/df2);
  const pInt=fTail(Fint,1,df2);
  // F de las pendientes: paralelas vs. separadas (1 restricción)
  const Fpend=((scrPar-scrNR)/1)/(scrNR/df2);
  const pPend=fTail(Fpend,1,df2);

  let h='<thead><tr><th>Hipótesis nula</th><th>Modelos comparados</th><th>F</th><th>p-valor</th><th>Al 5%</th></tr></thead><tbody>';
  h+=`<tr><td class="lbl">Todo igual (Chow)</td><td class="txt">Conjunta vs. dos regresiones separadas</td>`
   + `<td>${fmt(((scrR-scrNR)/2)/(scrNR/df2),2)}</td><td>${fmt(fTail(((scrR-scrNR)/2)/(scrNR/df2),2,df2),4)}</td>`
   + `<td>${fTail(((scrR-scrNR)/2)/(scrNR/df2),2,df2)<0.05?'<span class="badge no">rechaza</span>':'<span class="badge ok">no rechaza</span>'}</td></tr>`;
  h+=`<tr><td class="lbl">Mismo intercepto</td><td class="txt">Conjunta vs. rectas paralelas</td>`
   + `<td>${fmt(Fint,2)}</td><td>${fmt(pInt,4)}</td>`
   + `<td>${pInt<0.05?'<span class="badge no">rechaza</span>':'<span class="badge ok">no rechaza</span>'}</td></tr>`;
  h+=`<tr><td class="lbl">Misma pendiente</td><td class="txt">Rectas paralelas vs. dos regresiones separadas</td>`
   + `<td>${fmt(Fpend,2)}</td><td>${fmt(pPend,4)}</td>`
   + `<td>${pPend<0.05?'<span class="badge no">rechaza</span>':'<span class="badge ok">no rechaza</span>'}</td></tr>`;
  h+='</tbody>';
  $('#chDecomp').innerHTML=h;
}

function drawChow(){
  if(!chState) return;
  const {dat, rP, r0, r1}=chState;
  const c=setupCanvas('chCanvas', 0.45, 380);
  const pad={t:16,r:20,b:44,l:58};
  const yr=nicePad(Math.min(...dat.y), Math.max(...dat.y), 0.08);
  const sc=frame(c.ctx, c.cw, c.ch, pad, [5,21], yr, {xlab:'Educación (años)', ylab:'Salario por hora'});
  const ctx=c.ctx;
  scatterGroups(ctx, sc, dat.x, dat.y, dat.D, ['--accent','--red'], 2.3);
  drawLine(ctx, sc, x=>rP.b[0]+rP.b[1]*x, 5, 21, '--purple', 3.2, [7,4]);
  drawLine(ctx, sc, x=>r0.b[0]+r0.b[1]*x, 5, 21, '--accent', 2.6);
  drawLine(ctx, sc, x=>r1.b[0]+r1.b[1]*x, 5, 21, '--red', 2.6);
}

/* ══════════ Calculadora del test de Chow ══════════ */
function renderChowCalc(){
  const scrR=parseFloat($('#cwR').value);
  const s1=parseFloat($('#cw1').value), s2=parseFloat($('#cw2').value);
  const n=parseInt($('#cwN').value), k=parseInt($('#cwK').value);
  const alpha=parseFloat($('#cwA').value);
  const scrNR=s1+s2, df1=k, df2=n-2*k;
  const ok = isFinite(scrR)&&isFinite(scrNR)&&df2>0&&df1>0;
  const F = ok ? ((scrR-scrNR)/df1)/(scrNR/df2) : NaN;
  const p = ok ? fTail(F,df1,df2) : NaN;
  const fc = ok ? fCrit(alpha,df1,df2) : NaN;

  $('#cwStats').innerHTML=statCards([
    {l:'SCR no restringida', v:fmt(scrNR,3), c:'accent', note:`${fmt(s1,2)} + ${fmt(s2,2)}`},
    {l:'Reducción del SCR', v:fmt(scrR-scrNR,3), c:'green', note:'lo que ganan las dos regresiones separadas'},
    {l:'gl numerador (k)', v:String(df1), sm:true},
    {l:'gl denominador (n − 2k)', v:String(df2), sm:true},
    {l:'F de Chow', v:fmt(F,3), c:'purple'},
    {l:`F crítico al ${(alpha*100).toFixed(0)}%`, v:fmt(fc,3), sm:true},
    {l:'p-valor', v: p<0.0001?'<0.0001':fmt(p,4), c: p<alpha?'green':'orange'}
  ]);

  if(!ok){ $('#cwOut').innerHTML='<span>Revisá los valores cargados: n − 2k debe ser positivo.</span>'; return; }
  if(scrNR>scrR+1e-9){
    $('#cwOut').innerHTML='<span style="color:var(--red)"><strong>Algo está mal en los datos:</strong> el SCR de las regresiones separadas no puede superar al de la regresión conjunta. El modelo no restringido siempre ajusta al menos tan bien como el restringido.</span>';
    return;
  }
  const rech=p<alpha;
  $('#cwOut').innerHTML=
    `<span><strong>F = ${fmt(F,3)}</strong> contra F<sub>${df1},${df2}</sub> crítico de ${fmt(fc,3)} al ${(alpha*100).toFixed(0)}%: `
    + (rech
       ? `<strong style="color:var(--green)">se rechaza H₀</strong>. La función de regresión <strong>difiere</strong> entre los dos grupos. Paso siguiente: estimar con la dummy y sus interacciones para averiguar si lo que difiere es el nivel, las pendientes, o ambas cosas.`
       : `<strong style="color:var(--orange)">no se rechaza H₀</strong>. Los datos son compatibles con una única función de regresión para los dos grupos.`)
    + `</span>`;
}

/* ══════════════════════════════════════════════════════
   LAB 9 — Estimación a mano (Ejercicio 8)
   ══════════════════════════════════════════════════════ */
const HAND0=[
  {y:28, x:2, D:0}, {y:35, x:5, D:0}, {y:30, x:3, D:0}, {y:40, x:8, D:0},
  {y:45, x:2, D:1}, {y:52, x:5, D:1}, {y:48, x:3, D:1}, {y:60, x:8, D:1}
];
let HAND=HAND0.map(r=>({...r}));
function resetHand(){ HAND=HAND0.map(r=>({...r})); renderHand(); }
function handEdit(i, field, val){
  const v=parseFloat(val);
  if(isFinite(v)) HAND[i][field] = field==='D' ? (v>=0.5?1:0) : v;
  renderHand();
}

function renderHand(){
  let h='<thead><tr><th>Obs.</th><th>salario (y)</th><th>exper (x)</th><th>D (título)</th>'
      + '<th>x − x̄</th><th>D − D̄</th><th>y − ȳ</th></tr></thead><tbody>';
  const ybar=mean(HAND.map(r=>r.y)), xbar=mean(HAND.map(r=>r.x)), Dbar=mean(HAND.map(r=>r.D));
  HAND.forEach((r,i)=>{
    h+=`<tr><td class="lbl">${i+1}</td>`
     + `<td><input type="number" step="any" value="${r.y}" style="width:70px;font-family:inherit;font-size:.8rem;padding:.15rem .3rem;border:1px solid var(--border);border-radius:3px;background:var(--bg);color:var(--text)" onchange="handEdit(${i},'y',this.value)"></td>`
     + `<td><input type="number" step="any" value="${r.x}" style="width:60px;font-family:inherit;font-size:.8rem;padding:.15rem .3rem;border:1px solid var(--border);border-radius:3px;background:var(--bg);color:var(--text)" onchange="handEdit(${i},'x',this.value)"></td>`
     + `<td><input type="number" step="1" min="0" max="1" value="${r.D}" style="width:50px;font-family:inherit;font-size:.8rem;padding:.15rem .3rem;border:1px solid var(--border);border-radius:3px;background:var(--bg);color:var(--text)" onchange="handEdit(${i},'D',this.value)"></td>`
     + `<td>${fmt(r.x-xbar,3)}</td><td>${fmt(r.D-Dbar,3)}</td><td>${fmt(r.y-ybar,3)}</td></tr>`;
  });
  h+=`<tr class="hi"><td class="lbl">Medias</td><td>${fmt(ybar,4)}</td><td>${fmt(xbar,4)}</td><td>${fmt(Dbar,4)}</td><td colspan="3"></td></tr>`;
  h+='</tbody>';
  $('#hdData').innerHTML=h;

  let Sxx=0, SDD=0, SxD=0, Sxy=0, SDy=0;
  HAND.forEach(r=>{
    const dx=r.x-xbar, dD=r.D-Dbar, dy=r.y-ybar;
    Sxx+=dx*dx; SDD+=dD*dD; SxD+=dx*dD; Sxy+=dx*dy; SDy+=dD*dy;
  });
  const den=Sxx*SDD-SxD*SxD;
  const b1=(SDD*Sxy-SxD*SDy)/den;
  const d0=(Sxx*SDy-SxD*Sxy)/den;
  const b0=ybar-b1*xbar-d0*Dbar;

  $('#hdSums').innerHTML=statCards([
    {l:'S<sub>xx</sub>', v:fmt(Sxx,3), c:'accent'},
    {l:'S<sub>DD</sub>', v:fmt(SDD,3), c:'accent'},
    {l:'S<sub>xD</sub>', v:fmt(SxD,3), c: Math.abs(SxD)<1e-9?'green':'orange', note: Math.abs(SxD)<1e-9?'cero: x y D son ortogonales':'distinto de cero: x y D están correlacionadas'},
    {l:'S<sub>xy</sub>', v:fmt(Sxy,3), c:'purple'},
    {l:'S<sub>Dy</sub>', v:fmt(SDy,3), c:'purple'}
  ]);
  renderHandCoef(b0, d0, b1, Sxx, SDD, SxD, Sxy, SDy);
}

function renderHandCoef(b0, d0, b1, Sxx, SDD, SxD, Sxy, SDy){
  // Verificación con la rutina general de OLS
  const r=ols(HAND.map(o=>[1,o.D,o.x]), HAND.map(o=>o.y));
  $('#hdEq').innerHTML=`salario&#770; = ${fmt(b0,3)} + ${fmt(d0,3)}·D + ${fmt(b1,3)}·exper`;

  const p0=b0+b1*4, p1=b0+d0+b1*4;
  $('#hdCoef').innerHTML=statCards([
    {l:'β̂₁ (efecto de exper)', v:fmt(b1,4), c:'accent', note:'miles $ por año de experiencia'},
    {l:'δ̂₀ (efecto del título)', v:fmt(d0,4), c:'green', note:'diferencia a igual experiencia'},
    {l:'β̂₀ (intercepto)', v:fmt(b0,4), note:'sin título y con 0 años de experiencia'},
    {l:'Predicción: sin título, 4 años', v:fmt(p0,3), c:'accent'},
    {l:'Predicción: con título, 4 años', v:fmt(p1,3), c:'orange'},
    {l:'Verificación por OLS matricial', v: r && Math.abs(r.b[1]-d0)<1e-8 ? 'coincide' : 'revisar', c: r && Math.abs(r.b[1]-d0)<1e-8 ? 'green':'orange', sm:true, note:'las fórmulas cerradas y X′X⁻¹X′y dan lo mismo'}
  ]);

  drawHand(b0, d0, b1);

  const orto=Math.abs(SxD)<1e-9;
  const notes=[];
  if(orto){
    notes.push(`<div class="tip" style="margin-top:1rem"><strong>Con S<sub>xD</sub> = 0 las fórmulas se simplifican.</strong>
      β̂₁ = S<sub>xy</sub>/S<sub>xx</sub> = ${fmt(Sxy,2)}/${fmt(Sxx,2)} = <strong>${fmt(b1,4)}</strong> y δ̂₀ = S<sub>Dy</sub>/S<sub>DD</sub> = ${fmt(SDy,2)}/${fmt(SDD,2)} = <strong>${fmt(d0,4)}</strong>.
      Como la dummy y la experiencia no están correlacionadas en esta muestra, el coeficiente de cada una coincide con el de una regresión simple: no hay nada que "controlar".</div>`);
  } else {
    notes.push(`<div class="note" style="margin-top:1rem"><div class="note-title">Ahora los coeficientes se afectan mutuamente</div>
      Al editar los datos, S<sub>xD</sub> = ${fmt(SxD,3)} dejó de ser cero: la experiencia y el título están correlacionados en la muestra. Los dos numeradores dejan de ser separables y cada coeficiente se calcula <em>netando</em> el efecto del otro. Es exactamente el mecanismo del sesgo de variable omitida: si sacaras D del modelo, β̂₁ absorbería parte de su efecto.</div>`);
  }
  $('#hdNotes').innerHTML=notes.join('');
}

function drawHand(b0, d0, b1){
  const c=setupCanvas('hdCanvas', 0.4, 330);
  const pad={t:16,r:20,b:44,l:58};
  const xs=HAND.map(r=>r.x), ys=HAND.map(r=>r.y);
  const xr=nicePad(Math.min(...xs), Math.max(...xs), 0.12);
  const yr=nicePad(Math.min(...ys), Math.max(...ys), 0.12);
  const sc=frame(c.ctx, c.cw, c.ch, pad, xr, yr, {xlab:'Experiencia (años)', ylab:'Salario (miles $)'});
  const ctx=c.ctx;
  drawLine(ctx, sc, x=>b0+b1*x, xr[0], xr[1], '--accent', 2.6);
  drawLine(ctx, sc, x=>b0+d0+b1*x, xr[0], xr[1], '--red', 2.6);
  HAND.forEach(r=>{
    const yfit = b0 + d0*r.D + b1*r.x;
    ctx.strokeStyle=col('--text-sec'); ctx.lineWidth=1; ctx.setLineDash([2,2]);
    ctx.beginPath(); ctx.moveTo(sc.sx(r.x), sc.sy(r.y)); ctx.lineTo(sc.sx(r.x), sc.sy(yfit)); ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle=col(r.D?'--red':'--accent');
    ctx.beginPath(); ctx.arc(sc.sx(r.x), sc.sy(r.y), 5, 0, 2*Math.PI); ctx.fill();
    ctx.strokeStyle=col('--bg-canvas'); ctx.lineWidth=1.8; ctx.stroke();
  });
  ctx.fillStyle=col('--text-sec'); ctx.font='11px sans-serif'; ctx.textAlign='right';
  ctx.fillText('las líneas punteadas son los residuos', c.cw-pad.r, pad.t+12);
}

/* ══════════════════════════════════════════════════════
   Quiz V/F — Ejercicio 9 de la práctica
   ══════════════════════════════════════════════════════ */
const QUIZ=[
  {id:'a', q:'En un modelo con una variable dummy D, el coeficiente δ̂₀ mide la diferencia en la variable dependiente entre el grupo con D = 1 y el grupo base, <em>sin controlar por ninguna otra variable</em>.',
   ans:false, why:'La primera parte es correcta, la última no. En una regresión múltiple δ̂₀ mide la diferencia entre grupos <strong>manteniendo constantes todas las demás variables del modelo</strong>: es una lectura ceteris paribus como la de cualquier otro coeficiente. Solo en una regresión con la dummy <em>como único</em> regresor δ̂₀ coincide con la diferencia bruta de medias entre los dos grupos.'},
  {id:'b', q:'Si en una regresión de salario se incluyen las variables hombre y mujer simultáneamente junto con la constante, OLS no puede estimar el modelo.',
   ans:true, why:'Correcto: es la <strong>trampa de la variable dummy</strong>. Como hombre + mujer = 1 en toda observación, las dos columnas suman exactamente la constante y hay colinealidad perfecta. Se viola MLR.3, la matriz X′X es singular y no existe una solución única. Podés verlo en el Laboratorio 1 poniendo las tres dummies de región.'},
  {id:'c', q:'Si el coeficiente de una variable dummy no es significativo, entonces no hay diferencia alguna entre los dos grupos en la variable dependiente.',
   ans:false, why:'No significativo significa que <strong>estos datos no permiten distinguir el efecto de cero</strong>, no que el efecto sea cero. Puede haber una diferencia real que la muestra no detecta por falta de precisión: n chico, mucha varianza del error o poca variación en la dummy. Antes de concluir "no hay diferencia" hay que mirar el intervalo de confianza: si incluye valores económicamente grandes, el problema es de potencia, no de ausencia de efecto.'},
  {id:'d', q:'Con 4 categorías de ocupación (profesional, técnico, administrativo, obrero) debemos incluir 4 variables dummy en la regresión.',
   ans:false, why:'Van <strong>3</strong> dummies: la regla es g − 1. La cuarta categoría queda como grupo base y su efecto lo absorbe la constante. Incluir las cuatro junto con el intercepto reproduce la trampa del inciso b.'},
  {id:'e', q:'En el modelo ln(y) = β₀ + δ₀·D + β₁·x + u, si δ̂₀ = 0.45, entonces el grupo con D = 1 gana exactamente 45% más que el grupo base.',
   ans:false, why:'45% es la <strong>aproximación</strong>, y con un coeficiente tan grande es mala. El valor exacto es 100·(e^0.45 − 1) = <strong>56.8%</strong>, casi 12 puntos porcentuales más. La regla práctica: con |δ̂₀| menor a 0.10 la aproximación sirve; por encima de 0.15 hay que usar la fórmula exacta. Movelo en el Laboratorio 7.'},
  {id:'f', q:'En el modelo y = β₀ + δ₀·D + β₁·x + δ₁·D×x + u, si δ̂₁ = 0, las rectas de regresión para ambos grupos son coincidentes.',
   ans:false, why:'Con δ̂₁ = 0 las rectas son <strong>paralelas</strong>, no coincidentes: comparten la pendiente pero siguen teniendo interceptos distintos separados por δ̂₀. Para que sean coincidentes hacen falta <em>las dos</em> condiciones, δ₀ = 0 y δ₁ = 0, que es justamente la hipótesis conjunta del modelo de rectas coincidentes.'},
  {id:'g', q:'Cambiar el grupo base en un modelo con dummies altera el R² de la regresión.',
   ans:false, why:'No lo altera. Cambiar la base es una <strong>reparametrización</strong>: los valores ajustados, los residuos, el SCR, el SCT y por lo tanto el R² son idénticos. Lo único que cambia es qué diferencias quedan explícitas en los coeficientes y respecto de quién se miden. Verificalo en los Laboratorios 3 y 4.'},
  {id:'h', q:'Una interacción D×x en un modelo permite que la pendiente de x sea distinta para cada grupo definido por D.',
   ans:true, why:'Correcto, y es precisamente para lo que sirve. El efecto marginal de x es ∂y/∂x = β₁ + δ₁·D: vale β₁ en el grupo base y β₁ + δ₁ en el otro. El coeficiente δ₁ <em>es</em> la diferencia entre las dos pendientes, y su test t responde directamente si el rendimiento de x difiere entre grupos.'}
];

function renderQuiz(){
  $('#quizWrap').innerHTML=QUIZ.map((q,i)=>
    `<div class="quiz-item">
      <div class="quiz-q"><span class="qid">${q.id})</span>${q.q}</div>
      <div class="quiz-btns">
        <button class="btn btn-sm" onclick="answerQuiz(${i},true)">Verdadero</button>
        <button class="btn btn-sm" onclick="answerQuiz(${i},false)">Falso</button>
      </div>
      <div class="quiz-fb" id="qfb-${i}"></div>
    </div>`).join('');
  updateQuizScore();
}
let quizAnswers={};
function answerQuiz(i, val){
  const q=QUIZ[i];
  const ok=(val===q.ans);
  quizAnswers[i]=ok;
  const fb=$('#qfb-'+i);
  fb.className='quiz-fb show '+(ok?'ok':'no');
  fb.innerHTML=`<span class="quiz-verdict" style="color:var(${ok?'--green':'--red'})">${ok?'Correcto':'Incorrecto'} — la afirmación es ${q.ans?'VERDADERA':'FALSA'}</span>${q.why}`;
  updateQuizScore();
}
function updateQuizScore(){
  const done=Object.keys(quizAnswers).length;
  const right=Object.values(quizAnswers).filter(Boolean).length;
  $('#quizScore').textContent = done===0 ? '' : `Respondidas: ${done} de ${QUIZ.length} · Correctas: ${right}`;
}
function resetQuiz(){ quizAnswers={}; renderQuiz(); }

/* ══════════════════════════════════════════════════════
   Init y listeners
   ══════════════════════════════════════════════════════ */
function redrawAll(){
  drawDum();
  drawFlip();
  drawRegion();
  renderLinCode();
  renderLog();
  drawChow();
  renderHand();
}

let rzTimer=null;
window.addEventListener('resize', ()=>{
  clearTimeout(rzTimer);
  rzTimer=setTimeout(redrawAll, 120);
});
const mqDark=window.matchMedia('(prefers-color-scheme:dark)');
if(mqDark.addEventListener) mqDark.addEventListener('change', redrawAll);

renderCoder();
runDum();
runFlip();
renderRegion();
renderLinCode();
renderInter();
renderLog();
runChow();
renderChowCalc();
renderHand();
renderQuiz();
