#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void query(int i, int x){
    cout << "? " << i << " " << x << endl;
}

void solve()
{
    int n, tmp = 8;
    cin >> n;
    set<int> s, id;
    int msb = log2(n) + 2, rem = n;
    vector<int> cnt(msb, 0);
    for (int i = 1; i <= n; i++){
        s.insert(i);
        if(i!=n)
            id.insert(i);
        for (int j = 0; j < msb; j++){
            if(i&(1<<j))
                cnt[j]++;
        }
    }
    while(!id.empty()){
        vector<int> one, zero;
        int diff = inf, chosen = -1;
        for (int j = 0; j < msb; j++){
            int o = cnt[j], z = n - cnt[j];
            int curr_diff = abs(o-z);
            if(curr_diff<diff){
                chosen = j, diff = curr_diff;
            }
        }
        int cnto = 0, cntz = 0, t = (1<<chosen), in;
        for (auto &x: id){
            query(x, t);
            cin >> in;
            if(in){
                one.push_back(x);
                cnto++;
            }else{
                zero.push_back(x);
                cntz++;
            }
        }
        vector<int> ers;
        if(cnto==cnt[chosen]){
            for(auto &x: s){
                if(x&t){
                    ers.push_back(x);
                }
            }
            for(auto &x: one)
                id.erase(x);
        }else{
            for(auto &x: s){
                if((x&t)==0){
                    ers.push_back(x);
                }
            }
            for (auto &x : zero)
                id.erase(x);
        }
        n -= sz(ers);
        for(auto &x: ers){
            for (int j = 0; j < msb; j++){
                if(x&(1<<j))
                    cnt[j]--;
            }
            s.erase(x);
        }
    }
    cout << "! "<<*s.begin() << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}