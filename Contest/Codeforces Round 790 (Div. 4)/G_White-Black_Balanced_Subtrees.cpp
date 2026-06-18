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

int ans;
vector<vector<int>>t;
vector<int>color;
vector<pair<int,int>>sub;

void dfs(int node){
    if(color[node]){
        sub[node].ss++;
    }
    else sub[node].ff++;
    for(auto &x: t[node]){
        dfs(x);
        sub[node].ff+=sub[x].ff;
        sub[node].ss+=sub[x].ss;
    }
    if(sub[node].ff==sub[node].ss) ans++;
}


void solve()
{
    ans = 0;
    int n;
    cin>>n;
    color.resize(n+1);
    t.resize(n+1);
    sub.assign(n+1,{0,0});
    for(int i = 2; i<=n; i++){
        int p;
        cin>>p;
        t[p].pb(i);
    }
    string str;
    cin>>str;
    for(int i = 0; i<n; i++){
        color[i+1] = str[i]=='B';
    }
    dfs(1);
    cout<<ans<<endl;
    color.clear();
    t.clear();
    sub.clear();
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