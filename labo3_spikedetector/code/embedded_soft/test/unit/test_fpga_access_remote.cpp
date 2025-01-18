
#include <fcntl.h>
#include "fpgaaccessremote.hpp"
#include <arpa/inet.h>
#include <cstdint>
#include <gtest/gtest.h>
#include <netinet/in.h>
#include <sys/socket.h>

static int connect_to_server(uint16_t port)
{
	struct sockaddr_in addr;
	addr.sin_family = AF_INET;
	addr.sin_port = htons(port);

	int sockfd = socket(AF_INET, SOCK_STREAM, 0);
	assert(sockfd >= 0);
	assert(inet_pton(AF_INET, "127.0.0.1", &addr.sin_addr) > 0);
	assert(connect(sockfd, (struct sockaddr *)&addr, sizeof(addr)) >= 0);
	int flags = fcntl(sockfd, F_GETFL, 0);
	fcntl(sockfd, F_SETFL, flags | O_NONBLOCK);

	return sockfd;
}

TEST(TestFpgaAccessRemote, SetupStartServer)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1234 };
	FpgaAccessRemote access;

	struct sockaddr_in addr;
	addr.sin_family = AF_INET;
	addr.sin_port = htons(opts.port);

	int sockfd = socket(AF_INET, SOCK_STREAM, 0);
	ASSERT_GE(sockfd, 0);
	ASSERT_GT(inet_pton(AF_INET, "127.0.0.1", &addr.sin_addr), 0);
	ASSERT_LT(connect(sockfd, (struct sockaddr *)&addr, sizeof(addr)), 0);

	auto t = std::thread([&] { access.setup(opts); });
	t.join();

	ASSERT_GE(connect(sockfd, (struct sockaddr *)&addr, sizeof(addr)), 0);

	close(sockfd);
}

TEST(TestFpgaAccessRemote, EndTestMessageIsSent)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1235 };
	int socket;
	{
		FpgaAccessRemote access;
		auto t = std::thread([&] { access.setup(opts); });
		t.join();
		socket = connect_to_server(opts.port);
		shutdown(socket, SHUT_WR);
	}

	const char *expected_message = "end_test\n";
	char msg[50];

	size_t read_size;
	read_size = recv(socket, msg, sizeof(msg), 0);

	ASSERT_GE(read_size, strlen(expected_message));
	msg[read_size] = 0;
	ASSERT_STREQ(msg, expected_message);

	close(socket);
}
