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
vector<vector<int>> solutions;
int dp[(1ll<<8)][8][92], final_mask = (1ll<<8)-1;
vector<int> queenPos(8);
vector<pair<int,int>>queen_pos;

void find_solution(int row, int cols, int diag1, int diag2) {
    if (row == 8){
        solutions.push_back(queenPos);
        return;
    }
    int available = ((1 << 8) - 1) & ~(cols | diag1 | diag2);
    while (available) {
        int pos = LSOne(available);
        int col = __builtin_ctz(pos);
        queenPos[row] = col;
        available -= pos;
        find_solution(row + 1, cols | pos, (diag1 | pos) << 1, (diag2 | pos) >> 1);
    }
}

int distance(pair<int,int>&a, pair<int,int>&b){
    if(a==b)
        return 0;
    else if(a.ff==b.ff or a.ss==b.ss or abs(a.ff-b.ff)==abs(a.ss-b.ss))
        return 1;
    return 2;
}

int f(int mask, int row, int &curr_sol){
    if(mask==final_mask){
        return 0;
    }
    int &ans = dp[mask][row][curr_sol];
    if(ans!=-1)
        return ans;
    ans = inf;
    pair<int,int> row_pos = {row,solutions[curr_sol][row]};
    for(int i = 0; i<8; i++){
        if((mask&(1ll<<i))==0){
            pair<int,int>q_pos = queen_pos[i];
            ans = min(ans, distance(row_pos,q_pos) + f((mask|(1ll<<i)),row+1,curr_sol));
        }
    }
    return ans;
}

void solve()
{
    queen_pos.clear();
    memset(dp,-1,sizeof dp);
    int ans = inf;
    char c;
    for(int i = 0; i<8; i++){
        for(int j = 0; j<8; j++){
            cin>>c;
            if(c=='q')
                queen_pos.push_back({i,j});
        }
    }
    for(int i = 0; i<sz(solutions); i++){
        ans = min(ans,f(0,0,i));
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
    find_solution(0,0,0,0);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}