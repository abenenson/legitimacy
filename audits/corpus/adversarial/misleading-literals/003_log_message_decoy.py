def decide_tool_use(event, logger):
    logger.info("permit=false would have blocked legacy event")
    if event.get("tool") == "read_file":
        return "permit"
    return "escalate"

