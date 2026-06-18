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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
  void solve()
{
    int n;
    cin>>n;
    vector<int>v(n);
    readv(v);
    map<int,int>mp;
    for(auto &x: v){
        mp[x]++;
    }
    int cnt = 0, ti = -1, tj = -1,mxcnt = 0,ai = -1,aj = -1;
    for(int i = 0; i<n ;i++){
        int &x = v[i];
        if(mp[x]==1){
            if(cnt==0) ti = i;
            cnt++;
            tj = i;
        }else{
            if(cnt>mxcnt){
                mxcnt  = cnt;
                ai = ti;
                aj = tj;
            }
            cnt = 0;
        }
    }
    if(cnt>mxcnt){
        ai = ti;
        aj = tj;
    }
    if(ai==-1){
        cout<<0<<endl;
    }else{
        cout<<ai+1<<" "<<aj+1<<endl;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}