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

int msb(int x){
    return 63 - __builtin_clzll(x);
}

void solve()
{
    int n,q;
    cin >> n >> q;
    vector<int> ms(n), add_later;
    for(auto &x: ms)
        cin >> x;
    sort(all(ms));
    while(q--){
        int c, cost = 0;
        cin >> c;
        multiset<int> loss;
        while(c > 0){
            if(loss.empty() and ms.empty()){
                cost += c;
                break;
            }
            int target = (1 << msb(c));
            if(!loss.empty() and (ms.empty() or *loss.rbegin() > target or *loss.rbegin() > *ms.rbegin())){
                int val = *loss.rbegin();
                loss.erase(loss.find(val));
                if(val <= target){
                    cost += (target - val);
                    c -= target;
                    continue;
                }
                for(int i = target; i > 0; i >>= 1){
                    if((c & i) != 0 and (i <= val)){
                        val -= i;
                        c -= i;
                    }
                }
                loss.insert(val);
                continue;
            }
            int val = ms.back();
            add_later.push_back(val);
            ms.pop_back();
            if(val <= target){
                cost += (target - val);
                c -= target;
                continue;
            }
            for(int i = target; i > 0; i >>= 1){
                if((c & i) != 0){
                    int new_target = i;
                    if(val >= new_target){
                        val -= new_target;
                        c -= new_target;
                    }else if(ms.back() <= val){
                        cost += (new_target - val);
                        c -= new_target;
                        break;
                    }
                }
            }
            loss.insert(val);
        }
        cout << cost << endl;
        while(!add_later.empty()){
            ms.push_back(add_later.back());
            add_later.pop_back();
        }
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}