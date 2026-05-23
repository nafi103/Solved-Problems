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

struct Carrot{
    int x, p, improvement;

    Carrot(){}

    Carrot(int _x, int _p, int _improvement){
        x = _x;
        p = _p;
        improvement = _improvement;
    }

    bool operator<(const Carrot &other) const {
        return improvement < other.improvement;
    }
};

int get_cost(int x, int p){
    int base = x / p;
    int rem = x % p;
    return rem * (base + 1) * (base + 1) + (p - rem) * base * base;
}

void solve()
{
    int n, k;
    cin >> n >> k;

    Carrot carrot;
    priority_queue<Carrot> pq;

    int total_cost = 0;

    for(int i = 0; i < n; i++){
        cin >> carrot.x;
        total_cost += carrot.x * carrot.x;
        long long next_improvement = get_cost(carrot.x, 1) - get_cost(carrot.x, 2);
        carrot.p = 2;
        carrot.improvement = next_improvement;
        pq.push(carrot);
    }

    for(int i = 0; i < k - n; i++){
        Carrot curr = pq.top();
        pq.pop();

        total_cost -= curr.improvement;

        int next_improvement = get_cost(curr.x, curr.p) - get_cost(curr.x, curr.p + 1);
        curr.p++;
        curr.improvement = next_improvement;

        pq.push(curr);
    }

    cout << total_cost << endl;
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