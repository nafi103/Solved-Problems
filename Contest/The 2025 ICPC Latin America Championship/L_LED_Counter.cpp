#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;
 /****************************************************************/
 map<string, int> counter = {
  {"GGGgGGG",0},
  {"gggggGG",1},
  {"gGGGGGg",2},
  {"ggGGGGG",3},
  {"GggGgGG",4},
  {"GgGGGgG",5},
  {"GGGGGgG",6},
  {"ggGggGG",7},
  {"GGGGGGG",8},
  {"GgGGGGG",9}
};
 set<string>s;
 void f(int i, string tmp, string &str){
  if(sz(s)>1)
    return;
  if(i==7){
    if(counter.count(tmp))
      s.insert(tmp);
    return;
  }
  if(str[i]=='+' or str[i]=='-'){
    tmp.push_back('G');
    f(i+1,tmp,str);
    tmp.pop_back();
    tmp.push_back('g');
    f(i+1,tmp,str);
  }else{
    tmp.push_back(str[i]);
    f(i+1,tmp,str);
  }
}
 void solve()
{
    int n;
    cin>>n;
    for(int i = 0; i<n; i++){
      s.clear();
      string str;
      cin>>str;
      f(0,"",str);
      if(sz(s)>1)
          cout<<"*";
      else
        cout<<counter[*s.begin()];
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}