#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct Node
{
    int value;

    Node(int val = 0) : value(val) {}
};

Node merge(Node &left, Node &right)
{
    return Node(max(left.value , right.value));
}

struct Segment_Tree
{
    int n;
    vector<Node> st;

    Segment_Tree(int _n)
    {
        n = _n;
        st.resize(4 * n);
    }

    void update(int node, int b, int e, int &idx, Node &x)
    {
        if (e < idx or b > idx)
            return;
        if (b == idx and e == idx)
        {
            st[node] = Node(max(st[node].value, x.value));
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, idx, x);
        update(right, mid + 1, e, idx, x);
        st[node] = merge(st[left], st[right]);
    }

    Node query(int node, int b, int e, int l, int &r)
    {
        if (e < l or b > r)
            return Node();
        if (b >= l and e <= r)
        {
            return st[node];
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r), query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }
};

int query(int &l, int &r){
	cout << "? "<< l << " " << r << endl;
	int x;
	cin >> x;
	return x;
}


bool check(int x, int &n, Segment_Tree &st){
	int l = 1 , r = n, tr = n;
	while(l <= tr){
		int mid = (l + tr) / 2;
		int mex = query(mid , r);
		if(mex >= x)
			l = mid + 1;
		else
			tr = mid - 1;
	}
	l = tr;
	int tl = l;
	while(tl <= r){
		int mid = (tl + r) / 2;
		int mex = query(l, mid);
		if(mex >= x)
			r = mid - 1;
		else
			tl = mid + 1;
	}
	r = tl;
	return st.query(1,1,n,1,l).value >= r;
}

void solve()
{
    int n,q;
    cin >> n >> q;
    Segment_Tree st(n);
    while(q--){
    	int l,r;
    	cin >> l >> r;
    	Node x(r);
    	st.update(1,1,n,l,x);
    }
    int l = 1, r = n;
    while(l <= r){
    	int mid = (l + r) / 2;
    	if(check(mid, n, st))
    		l = mid + 1;
    	else
    		r = mid - 1;
    }
    cout << "! " << r << endl;
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