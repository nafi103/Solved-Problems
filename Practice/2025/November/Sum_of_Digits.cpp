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
int n;
pair<int,int> dp[11][2];
const pair<int,int> dummy = {-1,-1};
vector<int> num;

void process(int x){
    if(x == 0){
        num = {0};
        n = 1;
        for (int i = 0; i < n; i++)
        {
            for (int j = 0; j < 2; j++)
            {
                dp[i][j] = dummy;
            }
        }
        return;
    }
    num.clear();
    while (x > 0){
        num.push_back(x % 10);
        x /= 10;
    }
    reverse(all(num));
    n = sz(num);
    for (int i = 0; i < n; i++){
        for (int j = 0; j < 2; j++){
            dp[i][j] = dummy;
        }
    }
}

pair<int,int> f(int pos, int flag){ // first -> sum, second -> how_many
    if(pos == n){
        return make_pair(0,1);
    }
    pair<int, int> &ans = dp[pos][flag];
    if(ans!=dummy){
        return ans;
    }
    ans = {0, 0};
    int r = (flag == 0 ? num[pos] : 9);
    // vector<pair<int,int>> tmp;
    for (int i = r; i >= 0; i--){
        auto [sum,cnt] = f(pos + 1, (i == r ? flag : 1));
        // tmp.push_back({sum, cnt});
        ans.first += (sum + cnt * i);
        ans.second += cnt;
    }
    // debug(pos) debug(flag) debug(r) debug(tmp) debug(ans)
    return ans;
}
int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int a, b;
    while(cin>>a>>b and a!=-1){
        process(b);
        // debug(num)
        int ansr = f(0, 0).first;
        process(a > 0 ? a - 1 : 0);
        // debug(num)
        int ansl = f(0, 0).first;
        cout << ansr - ansl << endl;
    }
}