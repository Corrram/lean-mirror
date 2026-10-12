for (const [id, cls] of [['compare','comparing'],['detail','detailed']]) {
  const el = document.getElementById(id);
  el.addEventListener('change', () => document.body.classList.toggle(cls,el.checked));
}
document.addEventListener('click', event => {
  const link=event.target.closest('a[href^="#def-"]');
  if (!link) return;
  const target=document.querySelector(link.getAttribute('href'));
  if (target) { target.classList.remove('highlight'); requestAnimationFrame(()=>target.classList.add('highlight')); }
});
