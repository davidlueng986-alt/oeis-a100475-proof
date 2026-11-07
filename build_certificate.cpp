#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
uint32_t reverse_decimal(uint32_t x){uint32_t y=0;do{y=10*y+x%10;x/=10;}while(x);return y;}
int main(int argc,char**argv){
 const uint32_t B=60000;
 const string dest=argc>1?argv[1]:"certificate.tsv";
 // Trial division, not a sieve, enumerates every prime in increasing order.
 vector<uint32_t>primes;
 for(uint32_t candidate=2;primes.size()<B;candidate++){
  bool yes=true;
  for(uint32_t p:primes){if(uint64_t(p)*p>candidate)break;if(candidate%p==0){yes=false;break;}}
  if(yes)primes.push_back(candidate);
 }
 vector<uint32_t>f(B+1),rank(B+1),seen(B+1);
 for(uint32_t n=1;n<=B;n++)f[n]=reverse_decimal(primes[n-1]);
 uint32_t stamp=0;
 for(uint32_t n=1;n<=B;n++){
  if(rank[n])continue;
  stamp++;vector<uint32_t>path;uint32_t x=n;
  while(x<=B&&!rank[x]){
   if(x==0||seen[x]==stamp){cerr<<"CYCLE "<<x<<"\n";return 10;}
   seen[x]=stamp;path.push_back(x);x=f[x];
  }
  uint32_t level=x>B?0:rank[x];
  for(auto it=path.rbegin();it!=path.rend();++it)rank[*it]=++level;
 }
 ofstream out(dest);out<<"n\tp_n\tF_n\texit_steps\n";
 for(uint32_t n=1;n<=B;n++)out<<n<<"\t"<<primes[n-1]<<"\t"<<f[n]<<"\t"<<rank[n]<<"\n";
 auto rmax=*max_element(rank.begin(),rank.end());
 cout<<"{\"bound\":"<<B<<",\"prime_count\":"<<primes.size()<<",\"last_prime\":"<<primes.back()<<",\"max_exit_steps\":"<<rmax<<",\"algorithm\":\"trial division; arithmetic digit reversal; explicit exit ranks\"}\n";
}
