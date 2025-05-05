#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
int n,m;
vector<vector<char>>grid;
vector<vector<int>>dp,my_dp;

string ans = "",got_it = "";

int dx[] = {1,0,-1,0};
int dy[] = {0,1,0,-1};
char Move[] = {'D','R','U','L'};

bool valid(int i, int j, int d){
    return i>=0 and i<n and j>=0 and j<m and grid[i][j]!='#' and dp[i][j]>d;
}

bool valid2(int i, int j){
    return i>=0 and i<n and j>=0 and j<m and grid[i][j]!='#';
}

bool _last(int i, int j){
    return i==0 or j==0 or i==n-1 or j==m-1;
}


void solve()
{
    int r, c,ar = -1, ac = -1;
    cin>>n>>m;
    grid.resize(n,vector<char>(m));
    dp.assign(n,vector<int>(m,INT_MAX));
    my_dp.assign(n,vector<int>(m,INT_MAX));
    queue<array<int,3>>q;
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
            if(grid[i][j]=='A'){
                r = i,c = j;
            }else if(grid[i][j]=='M'){
                dp[i][j] = 0;
                q.push({i,j,0});
            }
        }
    }
    while(!q.empty()){
        auto [l,m,d] = q.front();
        q.pop();
        for(int i = 0; i<4; i++){
            int nr = l+dx[i], nc = m+dy[i];
            if(valid(nr,nc,d+1)){
                dp[nr][nc] = d+1;
                q.push({nr,nc,d+1});
            }
        }
    }
    q.push({r,c,0});
    my_dp[r][c] = 0;
    while(!q.empty()){
        auto [l,m,d] = q.front();
        q.pop();
        if(_last(l,m)){
            ar = l; ac = m;
            break;
        }
        for(int i = 0; i<4; i++){
            int nr = l+dx[i], nc = m+dy[i];
            if(valid(nr,nc,d+1) and my_dp[nr][nc]>d+1){
                my_dp[nr][nc] = d+1;
                q.push({nr,nc,d+1});
            }
        }
    }
    debug(my_dp)
    if(ar==-1){
        cout<<"NO"<<endl;
        return;
    }
    string ans = "";
    while(ar!=r or ac!=c){
        int pr, pc;
        for(int k = 0; k<4; k++){
            pr = ar+dx[k], pc = ac+dy[k];
            if(valid2(pr,pc) and my_dp[pr][pc]==my_dp[ar][ac]-1){
                ans.pb(Move[(k+2)%4]);
                break;
            }
        }
        ar = pr;
        ac = pc;
    }
    reverse(all(ans));
    cout<<"YES"<<endl;
    cout<<sz(ans)<<endl;
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