#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const pair<int,int> dummy = {-1 , -1}; 
vector<vector<pair<int,int>>> dp;
vector<vector<int>> t;
vector<int> parent, weight;
int n;

void input(){
    cin >> n;
    weight.resize(n);
    t.resize(n);
    parent.resize(n);
    dp.assign(n, vector<pair<int,int>>(2, dummy));
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}

pair<int,int> f(int node, int valid, int par){
    pair<int,int> &ans = dp[node][valid];
    parent[node] = par;
    if(ans != dummy)
        return ans;
    if(valid){
        ans = {1, sz(t[node])};
        for(auto &child: t[node]){
            if(child != par){
                auto [cnt, sum] = f(child, 0, node);
                ans.first += cnt;
                ans.second += sum;
            }
        }
    }else{
        ans = {0, 1};
        for(auto &child: t[node]){
            if(child != par){
                auto [cnt1, sum1] = f(child, 0, node);
                auto [cnt2, sum2] = f(child, 1, node);
                if(cnt1 > cnt2){
                    ans.first += cnt1;
                    ans.second += sum1;
                }
                else if(cnt2 > cnt1){
                    ans.first += cnt2;
                    ans.second += sum2;
                }
                else{
                    ans.first += cnt1;
                    ans.second += min(sum1, sum2);
                }
            }
        }
    }
    return ans;
}

void get_weight(int node, int valid){
    if(valid){
        weight[node] = sz(t[node]);
        for(auto &child: t[node]){
            if(child != parent[node]){
                get_weight(child, 0);
            }
        }
    }else{
        weight[node] = 1;
        for(auto &child: t[node]){
            if(child != parent[node]){
                auto &[cnt1, sum1] = dp[child][0];
                auto &[cnt2, sum2] = dp[child][1];
                if(cnt1 > cnt2)
                    get_weight(child, 0);
                else if(cnt1 < cnt2)
                    get_weight(child, 1);
                else if(sum1 < sum2)
                    get_weight(child, 0);
                else
                    get_weight(child, 1);
            }
        }
    }
}

void solve()
{
    input();
    if(n == 2){
        cout << "2 2\n1 1" << endl;
        return;
    }
    pair<int,int> ans1 = f(0, 0, -1);
    pair<int,int> ans2 = f(0, 1, -1);
    if(ans1.first > ans2.first){
        cout << ans1. first << " " << ans1.second << endl;
        get_weight(0, 0);
    }else if(ans2.first > ans1.first){
        cout << ans2. first << " " << ans2.second << endl;
        get_weight(0, 1);
    }else if(ans1.second < ans2.second){
        cout << ans1. first << " " << ans1.second << endl;
        get_weight(0, 0);
    }else{
        cout << ans2. first << " " << ans2.second << endl;
        get_weight(0, 1);
    }
    for(int i = 0; i < sz(t); i++){
        cout << weight[i] << " \n"[i == n - 1];
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}