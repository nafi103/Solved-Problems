#pragma GCC optimize("O3")
#pragma GCC optimize ("unroll-loops")
#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt")
#pragma GCC optimize("Ofast")
#pragma GCC target("abm,mmx,avx,avx2,fma,tune=native")
#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
#ifndef ONLINE_JUDGE
#include <algo/debug.h>
#else
#define debug(...) 42
#endif
typedef tree< int, null_type, less< int >, rb_tree_tag, tree_order_statistics_node_update > ordered_set;
template <typename T> istream& operator>>(istream& in, vector<T>& a) {for(auto &x : a) in >> x; return in;};
template <typename T> ostream& operator<<(ostream& out, vector<T>& a) {for(auto &x : a) out << x << ' '; return out;};
#define make_unique(x) sort(all(x)); x.resize(unique(all(x)) - x.begin())
string cdn[]{"NO","YES"};
#define int long long
#define vi vector<int>
#define pr pair<int,int>
#define all(x) x.begin(),x.end()
void solve();
int32_t main(){
 #ifndef ONLINE_JUDGE
  freopen("in.dat","r",stdin);
  freopen("out.dat","w",stdout);
  freopen("err.dat","w",stderr);
 #endif
 ios_base::sync_with_stdio(0);cin.tie(0);
 cout.tie(0);cout << fixed << setprecision(10);
 int tc = 1;
 for(int i=1;i<=tc;i++){
  solve();
 }
 return 0;
}
void solve(){
 int n,m,sum=0;
 cin >> n >> m;
 vi arr(n),presum;
 cin >> arr;
 for(auto ele :arr){
  sum += ele;
  presum.push_back(sum);
 }
  while(m--){
  int a;
  cin >> a;
  int dom = lower_bound(all(presum),a)-presum.begin();
  int room = a;
  if(dom !=0){
   room = a - presum[max(dom-1,0LL)];
  }
  cout << dom + 1 << " " << room <<endl;
  debug(dom,a,presum[max(dom-1,0LL)]);
 }
} 