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

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int dx[] = {1, 1,-1,-1,2, 2,-2,-2};
int dy[] = {2,-2, 2,-2,1,-1, 1,-1};
const int n = 8;

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<n;
}

void Queen_Mark(int i, int j, vector<vector<bool>>&mark){
    for(int k = 0; k<n; k++){
        mark[i][k] = true;
        mark[k][j] = true;
    }
    for(int r = i, c = j; r<n and c<n; r++,c++){
        mark[r][c] = true;
    }
    for(int r = i, c = j; r>=0 and c>=0; r--,c--){
        mark[r][c] = true;
    }
    for(int r = i, c = j; r>=0 and c<n; r--,c++){
        mark[r][c] = true;
    }
    for(int r = i, c = j; r<n and c>=0; r++,c--){
        mark[r][c] = true;
    }
}

void Rook_Mark(int i, int j, vector<vector<bool>>&mark){
    for(int k = 0; k<n; k++){
        mark[i][k] = true;
        mark[k][j] = true;
    }
}

void Bishop_Mark(int i, int j, vector<vector<bool>>&mark){
    for(int r = i, c = j; r<n and c<n; r++,c++){
        mark[r][c] = true;
    }
    for(int r = i, c = j; r>=0 and c>=0; r--,c--){
        mark[r][c] = true;
    }
    for(int r = i, c = j; r>=0 and c<n; r--,c++){
        mark[r][c] = true;
    }
    for(int r = i, c = j; r<n and c>=0; r++,c--){
        mark[r][c] = true;
    }
}

void Knight_Mark(int i, int j, vector<vector<bool>>&mark){
    mark[i][j] = true;
    for(int k = 0; k<8; k++){
        int ni = i+dx[k], nj = j+dy[k];
        if(valid(ni,nj)){
            mark[ni][nj] = true;
        }
    }
}

void King_Mark(int i, int j, vector<vector<bool>>&mark){
    mark[i][j] = true;
    int x[] = {1,1,1,-1,-1,-1,0,0};
    int y[] = {0,1,-1,0,1,-1,1,-1};
    for(int k = 0; k<8; k++){
        int ni = i+x[k], nj = j+y[k];
        if(valid(ni,nj)){
            mark[ni][nj] = true;
        }
    }
}

bool escape(int i, int j, vector<vector<bool>>&mark){
    if(!mark[i][j])
        return true;
    int x[] = {1,1,1,-1,-1,-1,0,0};
    int y[] = {0,1,-1,0,1,-1,1,-1};
    for(int k = 0; k<8; k++){
        int ni = i+x[k], nj = j+y[k];
        if(valid(ni,nj) and !mark[ni][nj]){
            return true;
        }
    }
    return false;
}

void solve()
{
    vector<vector<char>>grid(n,vector<char>(n));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cin>>grid[i][j];
        }
    }
    int x,y;
    cin>>x>>y;
    int r = 1, c = y-1;
    swap(grid[r-1][c],grid[r][c]);
    grid[r-1][c] = 'Q';
    vector<vector<bool>>mark(n,vector<bool>(n,false));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            if(grid[i][j]=='k'){
                r=i;c=j;
            }
            if(grid[i][j]=='Q')
                Queen_Mark(i,j,mark);
            else if(grid[i][j]=='R')
                Rook_Mark(i,j,mark);
            else if(grid[i][j]=='B')
                Bishop_Mark(i,j,mark);
            else if(grid[i][j]=='K')
                King_Mark(i,j,mark);
        }
    }
    if(!escape(r,c,mark)){
        cout<<'Q'<<endl;
    }else{
        cout<<'N'<<endl;
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