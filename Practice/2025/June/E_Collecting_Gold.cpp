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
vector<vector<int>>dp; //dp[i][j] -> i = mask, j = my curr_pos
vector<pair<int,int>>g;
pair<int,int>my_pos;
int final_mask,l;

int distance(pair<int,int>&a, pair<int,int>&b){
    return max(abs(a.ff-b.ff),abs(a.ss-b.ss));
}

int f(int mask, int pos){
    if(mask==final_mask){
        return distance(g[pos],g[l]);
    }
    int &ans = dp[mask][pos];
    if(ans!=inf){
        return ans;
    }
    for(int i = 0; i<l; i++){
        if((mask&(1ll<<i)) == 0){
            int new_mask = mask|(1ll<<i);
            ans = min(ans, distance(g[pos],g[i]) + f(new_mask, i));
        }
    }
    return ans;
}

void solve()
{
    g.clear();
    dp.clear();
    int n,m;
    cin>>n>>m;
    char c;
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>c;
            if(c=='g')
                g.push_back({i,j});
            else if(c=='x'){
                my_pos = {i,j};
            }
        }
    }
    l = sz(g);
    g.push_back(my_pos);
    final_mask = (1ll<<l) - 1;
    dp.resize(final_mask+1,vector<int>(l+1,inf));
    cout<<f(0,l)<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}