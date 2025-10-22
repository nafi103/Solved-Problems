#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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
vector<vector<int>>dp;
int n,m,r;

vector<vector<int>>states;

int f(int i, int j){
    if(i==n){
        return j==0;
    }
    int &ans = dp[i][j];
    if(ans!=-1)
        return ans;
    ans = 0;
    if(states[j].empty()){
        for(int p = 0; p<r; p++){
            bool flag = true;
            for(int q = 0; q<m; q++){
                if((j&(1<<q))==0 and (p&(1<<q))==0){
                    if(q<m-1 and ((j&(1<<(q+1)))==0 and (p&(1<<(q+1)))==0)){
                        q++;
                    }else{
                        flag = false;
                        break;
                    }
                }else if((j&(1<<q))!=0 and (p&(1<<q))!=0){
                    flag = false;
                    break;
                }
            }
            if(flag){
                states[j].push_back(p);
            }
        }
    }
    for(auto &x: states[j]){
        ans = (ans+f(i+1,x))%mod;
    }
    return ans;
}


int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    cin>>m>>n;
    r = 1<<m;
    states.resize(r);
    dp.assign(n,vector<int>(r,-1));
    cout<<f(0,0)<<endl;
}