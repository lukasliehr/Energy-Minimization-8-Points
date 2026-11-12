// Minimal exact integer matrix operations using GMP. No floating arithmetic.
#include <gmpxx.h>
#include <vector>
#include <cstddef>
#include <cstdint>
#include <algorithm>
#include <cstring>
struct Mat {size_t r,c;std::vector<mpz_class> a;Mat(size_t R,size_t C):r(R),c(C),a(R*C){}};
extern "C" {
void* gm_new(size_t r,size_t c,const unsigned char* data,size_t width) {
 try {auto* m=new Mat(r,c); if(data){for(size_t i=0;i<r*c;i++){auto* p=data+i*(width+1);mpz_import(m->a[i].get_mpz_t(),width,1,1,0,0,p+1);if(p[0])mpz_neg(m->a[i].get_mpz_t(),m->a[i].get_mpz_t());}}return m;}catch(...){return nullptr;}
}
void gm_delete(void* p){delete static_cast<Mat*>(p);}
void* gm_mul(void* pa,void* pb){
 try {auto&A=*static_cast<Mat*>(pa);auto&B=*static_cast<Mat*>(pb);if(A.c!=B.r)return nullptr;auto*C=new Mat(A.r,B.c);
  for(size_t i=0;i<A.r;i++)for(size_t k=0;k<A.c;k++){auto& a=A.a[i*A.c+k];if(a==0)continue;for(size_t j=0;j<B.c;j++){auto& b=B.a[k*B.c+j];if(b!=0)mpz_addmul(C->a[i*B.c+j].get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());}}
  return C;
 }catch(...){return nullptr;}
}
int gm_iadd(void* pa,void* pb){auto&A=*static_cast<Mat*>(pa);auto&B=*static_cast<Mat*>(pb);if(A.r!=B.r||A.c!=B.c)return 0;for(size_t i=0;i<A.a.size();i++)A.a[i]+=B.a[i];return 1;}
size_t gm_width(void* pa){auto&A=*static_cast<Mat*>(pa);size_t b=1;for(auto& x:A.a)b=std::max(b,(mpz_sizeinbase(x.get_mpz_t(),2)+7)/8);return b;}
int gm_export(void* pa,unsigned char* out,size_t width){auto&A=*static_cast<Mat*>(pa);if(width<gm_width(pa))return 0;memset(out,0,A.a.size()*(width+1));for(size_t i=0;i<A.a.size();i++){auto&x=A.a[i];auto*p=out+i*(width+1);p[0]=x<0;size_t count=(mpz_sizeinbase(x.get_mpz_t(),2)+7)/8;mpz_export(p+1+width-count,nullptr,1,1,0,0,x.get_mpz_t());}return 1;}
}
