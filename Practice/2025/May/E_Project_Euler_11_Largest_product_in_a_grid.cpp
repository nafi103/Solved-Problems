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
// #include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int x[] = {1,0,1,1};
int y[] = {0,1,1,-1};
vector<vector<int>>grid(20,vector<int>(20));

bool valid(int i, int j){
    return i>=0 and j>=0 and i<20 and j<20;
}

int check(int i, int j){
    if(!valid(i,j))
        return 0;
    return grid[i][j];
}

int f(int i, int j){
    int ans = 0;
    for(int k = 0; k<4; k++){
        int curr_ans = 1;
        for(int l = 0; l<4; l++){
            curr_ans*=check(i+x[k]*l, j+y[k]*l);
        }
        ans = max(ans,curr_ans);
    }
    return ans;
}

void solve()
{
    int ans = 0;
    for(auto &x: grid){
        readv(x);
    }
    for(int i = 0; i<20; i++){
        for(int j = 0; j<20; j++){
            ans = max(ans,f(i,j));
        }
    }
    cout<<ans<<endl;
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
        // google(z);
        solve();
    }
}