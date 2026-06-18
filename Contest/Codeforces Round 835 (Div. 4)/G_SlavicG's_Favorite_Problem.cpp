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
using pii = pair<int,int>;
vector<vector<pii>>t;
bool flag = false;
vector<set<int>>s;

void dfs(int node, int parent, int _xor, int des, int type){
    if(!type and node==des){
        if(_xor==0){
            flag = true;
        }
        return;
    }
    if(parent!=-1){
        s[type].insert(_xor);
    }
    for(auto &[child,weight]: t[node]){
        if(child!=parent){
            dfs(child,node,(_xor^weight),des,type);
        }
    }
}


void solve()
{
    flag = false;
    s.clear();
    t.clear();
    int n,a,b;
    cin>>n>>a>>b;
    s.resize(2);
    t.resize(n+1);
    for(int i = 1; i<n; i++){
        int u,v,w;
        cin>>u>>v>>w;
        t[u].pb({v,w});
        t[v].pb({u,w});
    }
    dfs(a,-1,0,b,0);
    dfs(b,-1,0,a,1);
    s[0].insert(0);
    if(flag){
        yes;
        return;
    }
    debug(s)
    for(auto &x:s[0]){
        if(s[1].count(x)){
            flag = true;
            break;
        }
    }
    if(flag)
        yes;
    else
        no;
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